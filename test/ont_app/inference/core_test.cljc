(ns ont-app.inference.core-test
  (:require
   #?(:cljs [cljs.test :refer-macros [async deftest is testing]]
      :clj [clojure.test :refer :all])
   [ont-app.igraph.core :as igraph :refer [add]]
   [ont-app.igraph.graph :as graph :refer [make-graph]]
   [ont-app.inference.core :as infer]
   ))


(def model (add (make-graph)
                [[::me ::hasParent ::Dad]
                 [::me ::hasParent ::Mom]
                 [::Dad ::hasBrother ::Sam]
                 [::Mom ::hasBrother ::Fester]
                 ]))

(def rules (add (make-graph)
                [[::Uncle
                  :rdf/type :infer/Rule
                  :infer/antecedent
                  [[:?self ::hasParent :?parent]
                   [:?parent ::hasBrother :?uncle]]
                  ;; ->
                  :infer/consequent
                  [[:add :?self ::hasUncle :?uncle]]]]))

(deftest simple-test
  (testing "Simple uncle test"
    (let [result (infer/apply-only rules model ::Uncle)
          ]
      (is (= (result ::me ::hasUncle)
             #{::Sam ::Fester})))))
