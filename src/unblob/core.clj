(ns unblob.core
  (:require [clojure.string :as s])
  (:import [java.nio.charset Charset]
           [java.nio.channels FileChannel Channels ReadableByteChannel]
           [java.nio IntBuffer ByteBuffer ByteOrder])
  (:gen-class))


(defrecord
                                        ;"record for serialization of a stock quote"
    Quote [^long timestamp ^String ticker ^long ask_size ^double ask_price ^long bid_size ^double bid_price
           ^boolean pre_post_market_session ^boolean halted])

(def ^:private global-header (+ 4 2 2 4 4 4 4))
(def ^:private pcap-header (+ 4 4 4 4))
(def ^:private pcap-header-size (+ 4 4 4 4))
(def ^:private pcap-packet-len-addr (+ 4 4))
(def ^:private ethernet-header 14)
(def ^:private ipv4-len-addr 2)
(def ^:private distance-to-body 12)

(declare refill-buffer!)
(declare skip-bytes!)


(def ^:private quote-update-frame
  [[:grab
    {:size :u1, :endianess :little, :datum-name :flags, :transform identity}]
   [:grab
    {:size :u8,
     :endianess :little,
     :datum-name :timestamp,
     :transform identity}]
   [:grab
    {:size 8,
     :endianess :little,
     :datum-name :ticker,
     :transform #(s/trim (String. ^bytes % (Charset/forName "US-ASCII")))}]
   [:grab
    {:size :u4, :endianess :little, :datum-name :bid-size, :transform identity}]
   [:grab
    {:size :u8,
     :endianess :little,
     :datum-name :bid-price,
     :transform identity}]
   [:grab
    {:size :u8,
     :endianess :little,
     :datum-name :ask-price,
     :transform identity}]
   [:grab
    {:size :u4,
     :endianess :little,
     :datum-name :ask-size,
     :transform identity}]])

(def ^:private quote-update-whole [[:grab-quote {:size 41, :datum-name :quote-record}]])

(def ^:private process-message
  [[:ensure 3]
   [:grab {:size :u2, :endianess :little, :datum-name :message-length}]
   [:grab {:size :u1, :endianess :little, :datum-name :message-type}] ;(operand
                                                                      ;buffer
                                                                      ;parse
                                                                      ;in-channel)
   [:ensure-message-length]
   [:grab-cond
    {:size :message-length,
     :datum-name :data,
     :switch-on :message-type,
     :mappings {0x51 quote-update-whole}}]])


(def ^:private to-iex
  [[:ensure 98] ;(+ 8 4 4 14 1 1 2 16 0 8 12 2 2 24)
   [:skip pcap-packet-len-addr]
   [:grab {:size :u4, :endianess :little, :datum-name :bytes-of-pcap}]
   [:grab {:size :u4, :endianess :little, :datum-name :bytes-of-pcap2}]
   [:skip ethernet-header] [:grab-ihl] [:skip 1]
   [:grab {:size :u2, :endianess :big, :datum-name :bytes-of-ip}] [:skip 16]
   [:skip-custom-ihl] [:skip 8] [:skip 12]
   [:grab {:size :u2, :endianess :little, :datum-name :list-length}]
   [:grab {:size :u2, :endianess :little, :datum-name :list-count}] [:skip 24]
   [:process-list {:item-instructions process-message, :datum-name :iex-list}]])

(def ^:private pcap-list [[:global-header]
                          [:grab-list-lazy {:item-instructions to-iex}]])

(def ^:private CAPACITY 7000)


(defn- fill-buffer!
  [file-buffer in-channel]
  (.clear file-buffer)
  (loop [total-bytes 0]
    (let [read-bytes (.read in-channel file-buffer)
          total-bytes (+ read-bytes total-bytes)]
      (if-not (or (= read-bytes -1) (= total-bytes CAPACITY))
        (recur total-bytes))))
  (.flip file-buffer))

(defn- refill-buffer!
  ^long [^ByteBuffer file-buffer ^ReadableByteChannel in-channel ensure-length]
  (if (>= (+ (.position file-buffer) ensure-length) (.limit file-buffer))
    (do (.compact file-buffer)
        (let [exit-code
                (loop [total-bytes (.position file-buffer)]
                  (let [read-bytes (.read in-channel file-buffer)
                        total-bytes (+ read-bytes total-bytes)]
                    (cond  (neg? read-bytes) (do (.limit file-buffer total-bytes) 0)
                           (= total-bytes CAPACITY) CAPACITY
                           :else  (recur total-bytes))))]
          (.rewind file-buffer)
          exit-code))
    CAPACITY))

(defn- skip-bytes!
  [^ByteBuffer buffer num-bytes]
  (.position buffer (int (+ (.position buffer) num-bytes))))

(defmulti ^:private process-command
  (fn [instructions control-data buffer parse in-channel]
    (ffirst instructions)))

(defmethod ^:private process-command :grab-quote
  [[[op {:keys [item-instructions datum-name]} & instructions]] control-data
   buffer parse in-channel]
  `(let [flags# (bit-and (.get ~buffer) 0xff)
         timestamp# (.getLong ~buffer)
         ticker-byte-array# (byte-array 8)
         _# (.get ~buffer ticker-byte-array#)
         ticker# (s/trim (String. ticker-byte-array#
                                  (Charset/forName "US-ASCII")))
         bid-size# (bit-and (.getInt ~buffer) 0xffffffff)
         bid-price-raw# (.getLong ~buffer)
         ask-price-raw# (.getLong ~buffer)
         bid-price# (/ bid-price-raw# 4.0)
         ask-price# (/ ask-price-raw# 4.0)
         ask-size# (bit-and (.getInt ~buffer) 0xffffffff)
         pre-post-market-session# (boolean (not= (bit-and flags# 0x40) 0))
         halted# (boolean (not= (bit-and flags# 0x80) 0))]
     (Quote. timestamp#
              ticker#
              ask-size#
              ask-price#
              bid-size#
              bid-price#
              pre-post-market-session#
              halted#)))


(defmethod ^:private  process-command :grab-ihl
  [[{:keys [size datum-name endianess transform]} & instructions] control-data
   buffer parse in-channel]
  (let [ihl-bytes-sym (gensym 'ihl-bytes)]
    `(do (.order ~buffer ByteOrder/BIG_ENDIAN)
         (let [~ihl-bytes-sym (* (bit-and (bit-and (.get ~buffer) 0xff) 0xf) 4)]
           ~(process-command instructions
                             (assoc control-data :ihl-bytes ihl-bytes-sym)
                             buffer
                             parse
                             in-channel)))))

(defmethod ^:private process-command :grab-list-lazy
  [[[op {:keys [item-instructions]}]] control-data buffer parse in-channel]
  `(letfn [(process-list-lazy#
             []
             (lazy-seq
               (when-let [parsed-packet# ~(process-command item-instructions
                                                           control-data
                                                           buffer
                                                           parse
                                                           in-channel)]
                 (cons parsed-packet# (process-list-lazy#)))))]
     (process-list-lazy#)))

(defmethod ^:private process-command :ensure
  [[instruction & instructions] control-data buffer parse in-channel]
  `(if (pos? (refill-buffer! ~buffer ~in-channel ~(last instruction)))
      ~(process-command instructions control-data buffer parse in-channel)))

(defmethod ^:private process-command :skip
  [[instruction & instructions] control-data buffer parse in-channel]
  `(do (skip-bytes! ~buffer ~(last instruction))
       ~(process-command instructions control-data buffer parse in-channel)))

(defn ^:private astore
  [len expr]
  (let [ret (with-meta (gensym 'ret) {:tag 'objects})]
    `(loop  [idx# 0 ~ret (make-array Quote ~len)]
       (if (= idx# ~len)
         ~ret
          (let [val# ~expr]
            (if (instance? Quote val#)
                (aset ~ret idx# val#))
            (recur (unchecked-inc idx#) ~ret))
          ))))

(defmethod ^:private process-command :process-list
  [[[op {:keys [item-instructions datum-name]} & instructions]] control-data
   buffer parse in-channel]
  (astore (:list-count control-data)  (process-command item-instructions
                                                       control-data
                                                       buffer
                                                       parse
                                                       in-channel)))

(defmethod ^:private process-command :ensure-message-length
  [[instruction & instructions] control-data buffer parse in-channel]
  (let [message-length-sym (:message-length control-data)]
    `(let [exit-code# (refill-buffer! ~buffer ~in-channel ~message-length-sym)]
       (if (pos? exit-code#)
         (do ~(process-command instructions
                               control-data
                               buffer
                               parse
                               in-channel))))))

(defmethod ^:private process-command :skip-custom-ihl
  [[instruction & instructions] control-data buffer parse in-channel]
  (let [ihl-bytes-sym (:ihl-bytes control-data)]
    `(do (if (> ~ihl-bytes-sym 20) (skip-bytes! ~buffer (- ~ihl-bytes-sym 20)))
         ~(process-command instructions control-data buffer parse in-channel))))



(defmethod ^:private process-command :global-header
  [[instruction & instructions] control-data buffer parse in-channel]
  `(do
    (fill-buffer! ~buffer ~in-channel)
    (skip-bytes! ~buffer global-header)
    ~(process-command instructions control-data buffer parse in-channel)))

(defmethod ^:private process-command :grab
  [[[_ {:keys [size endianess datum-name]}] & instructions] control-data buffer
   parse in-channel]
  (let [grabbed (gensym (symbol datum-name))]
    `(do ~(case endianess
            :little `(.order ~buffer ByteOrder/LITTLE_ENDIAN)
            :big `(.order ~buffer ByteOrder/BIG_ENDIAN))
         (let [~grabbed ~(case size
                           :u8 `(.getLong ~buffer)
                           :u4 `(bit-and (.getInt ~buffer) 0xffffffff)
                           :u2 `(bit-and (.getShort ~buffer) 0xffff)
                           :u1 `(bit-and (.get ~buffer) 0xff)
                           `(let [output# (byte-array ~size)]
                              (.get ~buffer output#)
                              output#))]
           ~(process-command instructions
                             (assoc control-data datum-name grabbed)
                             buffer
                             parse
                             in-channel)))))


(defmacro ^:private defnparse
  [varname parse-instructions]
  (let [buffer-sym (with-meta (gensym 'buffer) {:tag `ByteBuffer})
        in-channel-sym (gensym 'in-channel)]
    `(defn ~varname
       [~buffer-sym ~in-channel-sym]
       ~(process-command (eval parse-instructions)
                         {}
                         buffer-sym
                         {}
                         in-channel-sym))))

(defmethod ^:private process-command :grab-cond
  [[[op {:keys [datum-name mappings switch-on]}]] control-data buffer parse
   in-channel]
  (let [message-type-sym (:message-type control-data)]
    `(case  (int ~message-type-sym)
       0x51 ~(process-command quote-update-whole
                                           control-data
                                           buffer
                                           parse
                                           in-channel)
                    (skip-bytes! ~buffer (unchecked-dec ~(:message-length control-data))))
       ))

(defnparse parsing-machine pcap-list)


;;20170826.pcap something wrong with file
;(process-files)
(comment (time (process-files)))
(comment (ns-unmap *ns* 'process-command))
(comment (ns-unmap *ns* 'skip-bytes!))
(comment (clojure.pprint/pprint
           (process-command pcap-list {} 'buffer 'parse 'in-channel)))
(comment (ns-unmap *ns* 'process-command))
(comment (clojure.pprint/pprint (macroexpand-1 '(defnparse parsing-machine pcap-list))))


;(clojure.pprint/pprint (e/emit-form (ana.jvm/analyze  (macroexpand-1 '(defnparse parsing-machine pcap-list)))))
