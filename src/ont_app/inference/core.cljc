(ns ont-app.inference.core
    (:require
     [clojure.string :as str]
     [clojure.set :as set]
     ;; 3rd party libraries
     [selmer.parser :as selmer]
     [taoensso.timbre :as timbre]
     ;; ont-app libraries
     [ont-app.inference.ont :as ont]
     [ont-app.graph-log.core :as glog
      :refer [log
              log-graph
              log-reset!
              log-value
              ]]
     [ont-app.igraph.core :as igraph
      :refer [add
              difference
              disjoint-traversal
              query
              subtract
              traverse
              ]]
     [ont-app.igraph.graph :as g :refer [make-graph]]
     [ont-app.igraph-vocabulary.core :as igv]
     [ont-app.vocabulary.core :as voc]
     ))

(voc/cljc-put-ns-meta!
 'ont-app.inference.core
 {
  :voc/mapsTo 'ont-app.inference.ont
  }
 )

(def ontology ont/ontology)
(def validator ont/validator)

;; FUN WITH READER MACROS

#?(:cljs
   (enable-console-print!)
   )

#?(:cljs
   (defn on-js-reload [] )
   )

;; NO READER MACROS BEYOND THIS POINT

(def the igraph/unique)

(def empty-graph (make-graph))

(def initial-log-graph
  (add
   empty-graph
   [[:log/eventID :rdf/type :log/InformsKwi]
    [:log/ruleID :rdf/type :log/InformsKwi]
    [:log/AfterBindingTest :log/supportsDiagnostic :infer/diag-partial-binding]
    ]))

(declare mint-kwi)



(defn locally-bound-vars [rules rule]
  "Returns {<var> <value>, ...} for :?variables specified directly in <rule> which are not special bindings."
  (letfn [(collect-local-binding [acc _var]
            (assoc acc _var (the (rules rule _var))))
          (special-binding? [p]
            (contains? (set
                        (the
                         (rules
                          rule
                          :infer/specialBindings)))
                       p))
          ]
    (log-value
     ::LocallyBoundVarsReturn [:log/ruleID rule]
     (reduce collect-local-binding
             {}
             (->> (rules rule)
                  (keys)
                  (filter (fn [p]
                            (and (g/kw-starts-with-? p)
                                 (not (special-binding? p))))))))))

       

(defn local-bindings [rules rule pattern-property]
  "Returns <clauses> for `rule` in `rules` `pattern-property` with <var> bindings swapped in.
Where
<clauses> := [<clause>, ...] an antecedent or consequent specification
<rule> identifies a rule in <rules>
<rules> := {<rule> <desc>, ...}
<pattern-property> :~ #{:infer/antecedent :infer/consequent}
<clause> := [<elt>, ...]
  with any local variable bindings swapped in for <var>s.
<var> is a :?variable
<elt> is a <var> or <value>
<desc> := {:infer/antecedent #{<query-spec>}
           :infer/specialBinding #{<special var>} (special vars are ignored)
           <var> #{<value>} (optional)
           <special var> #{(fn [model bmap]...) -> <value>} (not affected here)
           ...
          }
<value> is a graph element in the model to which <rule> is being applied.
"
  {:pre [#{:infer/antecedent :infer/consequent} pattern-property]
   }
  (let [desc (rules rule)
        locally-bound (locally-bound-vars rules rule)
        ]
    (letfn [(substitute-elt [elt]
              (or (locally-bound elt)
                  elt))
            (substitute-local-bindings [clause]
              (->> (map substitute-elt clause)
                   (into [])))
            ]
      (log-value
       :log/LocalBindingsReturn
       [:log/ruleID rule
        :log/locallyBound locally-bound
        :log/patternProperty pattern-property
        ]
       (->> (the (desc pattern-property))
            (map substitute-local-bindings)
            (into []))))))

;; matching support...
(defn get-rule-index [rules]
  "Returns <match-index>  for `rules`
  ... used for quick lookup of rules pertinent some delta spec full of values
Where
<match-index> := {<value> #{<rule>, ...}, ...}
<value> is a non-:?var in the <antecedent> of some <rule>
<rule> names a rule in <rules>, with an <antecedent>
<antecedent> is a query specification [<clause>, ...]
<clause> := [<elt> <elt> <elt>]
<rules> is a graph of rule prototypes defined with the rules ontology
<elt> is a ?:var or a <value>
"
  (letfn [(collect-traverses-over [rule index traverses-over]
            ;; functional predicates should have a traversesOver
            ;; declaration when they appear in rules.
            ;; so that they are indexed properly
            (assoc index traverses-over rule))
          
          (collect-value [rule index elt]
            ;; adds <elt> <rule> to <index> as appropriate
            (if (not (g/kw-starts-with-? elt)) ;; TODO use spec
              (if (fn? elt)
                (if-let [traverses-over (rules elt :infer/traversesOver)]
                  (reduce (partial collect-traverses-over rule)
                          traverses-over)
                  ;; else no traverses-over declaration
                  index)
                ;; else it's not a var or a fn
                (assoc index elt (conj (or (index elt) #{})
                                       rule)))
              ;; else it's a var, don't index
              index))
          
          (collect-clause [rule index clause]
            ;; adds non-var elements of clause to index
            (reduce (partial collect-value rule) index clause))
          
          (collect-antecedent [index bmap]
            ;; adds non-var elements of antecedent to index
            ;; where bmap := {:rule... :antecedent...}
            (reduce (partial collect-clause (:?rule bmap))
                    index
                    (local-bindings rules (:?rule bmap) :infer/antecedent)))
          ]
    (reduce collect-antecedent
            {}
            (query rules [[:?rule :infer/antecedent :?antecedent]])
            )))

(defn binding-test [rules model rule]
  "Returns fn [bmap] -> boolean for `rule` in `rules` applied to `model`
Where
<bmap> is an antecedent binding for <rule>, including special bindings
<rule> names a rule in <rules>, which may have a rules/test clause naming one
  or more elaborations of :infer/TestFunction
<rules> is an IGraph informed by the rules ontology
<model> is the IGraph from which <bmap> has been acquired.
NOTE: typically used for filtering the set of <bmaps> in get-matches.
"
  (let [tests (rules rule :infer/test)
        ]
    (fn [bmap]
      (loop [tests tests]
        (if (empty? tests)
          true
          (let [test-fn (the (rules (first tests) :igraph/compiledAs))
                ]
            (when (not test-fn)
              (throw (ex-info (str "No compiled function for " (first tests))
                              {:type :no-compiled-test-function
                               :rules rules
                               :rule rule
                               :test-id (first tests)
                               })))
            (if (not (test-fn model bmap))
              false
              (recur (rest tests)))))))))
                
           
(defn get-matches [model context]
  "Returns [context, #{<match-spec>, ...}] for `model` in traversal `context`
Where:
<match-spec> := {:rule <rule>
                 :bindings #{<bmap>, ...}
                 }
<context> := {:rules... :index... :rule-candidates... :match-history..., ...}
   the context of an implications* traversal
<rules> is a graph of rule specifications defined with the rules ontology
<index> := {<value> #{<rule>, ...}, ...}
  ... used for quick lookup of rules pertinent to <next-delta>
<rule-candidates-fn> := (fn [context] ...) -> [<rule>, ...]
  (optional) defaults to returning all rules.
<match-history> := {<rule> : #{<binding>, ...}, ...}, encounterd 
  previously during the traversal <context>
<rule> names a rule specification in <rules>, with <antecedent> and <consquent>
<antecedent> is a query specification [<clause>, ...]
<bmap> := {<var>, <value>, ...}, matching <antecedent> of <rule> in <model>
<var> is a :?var in the <antecedent> of <rule>
<value> is a non-var in the <antecedent> of <rule>
<clause> := [<elt> <elt> <elt>]
<elt> is a ?:var or a <value>

NOTE: typically used to infer new assertions implied by the addition of 
  changes involving <visited-values> to <model>.
"
  (let [consequent (disjoint-traversal :infer/consequent :infer/consequentFn)
        {index :index
         rules :rules
         rule-candidates :rule-candidates
         match-history :match-history
         :or {rule-candidates (fn [context] ;; all rules
                                (let [bmaps
                                      (query
                                       (:rules context)
                                       [[:?rule :infer/antecedent :?antecedent]
                                        [:?rule consequent :?consequent]])
                                      ]
                                  (map :?rule bmaps)))
              }
         } context
        ]
    (letfn [(collect-rule-bindings [rule-bindings next-rule]
              ;; returns #{{:rule... :bindings ...}, ...}
              (timbre/debug "Next Rule: " next-rule)
              (log :log/StartCollectingRules :log/ruleID next-rule)
              (let [binding-history (and match-history
                                         (match-history next-rule))
                    locally-bound (locally-bound-vars rules next-rule)
                    _ (log :log/LocallyBound
                               :log/ruleID next-rule
                               :log/locallyBound locally-bound)

                    antecedent (if (not (empty? locally-bound))
                                   (local-bindings rules
                                                   next-rule
                                                   :infer/antecedent)
                                   ;; else no local bindings
                                   (the (rules next-rule :infer/antecedent)))
                    bmaps (query model antecedent)
                    _ (log :log/AfterQueryingWithLocals
                           :log/bmaps bmaps
                           )
                    bmaps (if (not (empty? locally-bound))
                             (map (fn [bmap] (merge bmap locally-bound))
                                  bmaps)
                             bmaps)
                    _ (log :log/AfterMergingLocallyBound
                           :log/ruleID next-rule
                           :log/bmaps bmaps)

                    bmaps (into
                           #{}
                           (filter (binding-test rules model next-rule) bmaps))
                    _  (log :log/AfterBindingTest
                            :log/antecedent antecedent
                            :log/bmaps bmaps
                            :log/context context
                            :log/locally-bound locally-bound
                            :log/model model
                            :log/ruleID next-rule
                            )
                    bmaps (if binding-history
                            (set/difference bmaps binding-history)
                            bmaps)
                    ]

                (if (empty? bmaps)
                  (let []
                    (log :log/EmptyRuleMatches :log/ruleID next-rule)
                    rule-bindings)
                  ;; else
                  (let []
                    (log :log/GotMatches :log/ruleID next-rule :log/bmaps bmaps)
                    (conj rule-bindings {:rule next-rule
                                         :bindings bmaps})))))
            
            
            (collect-match-history [match-history next-match-spec]
              ;; <next-match-spec> := {:rule..., :bindings...}
              ;; <match-history> := {<rule> <bindings>, ...}
              (let [{rule :rule
                     bindings :bindings
                     } next-match-spec
                    ]
                (assoc match-history
                       rule
                       (reduce conj
                               (or (match-history rule) #{})
                               bindings))))
            ]
      (let [rule-bindings (reduce collect-rule-bindings #{}
                                  (rule-candidates context)
                                  )
            match-history (reduce collect-match-history
                                  (or match-history {})
                                  rule-bindings)
            ]
        (log-value
         :log/GetMatchesReturn
         [(assoc context :match-history match-history),
          rule-bindings])))))


^:reduce-fn
(defn collect-delta-graphs [[to-remove to-add] next-delta]
  "Returns [<to-remove>' <to-add>'] modified for <next-delta>
Where
<to-remove>, <to-add> implement IGraph, and describe edits scheduled for 
  some model in response to one or more rule applications pertinent to a 
  the current state of some model.
<next-delta> := [<op> <s> <p> <o>], a clause in a vector of deltas
<op> :~ #{:add :subtract}
"
  (let [[op s p o] next-delta
        ]
    (case op
      :add [to-remove (add to-add [s p o])]
      :subtract [(add to-remove [s p o]) to-add])))    

(defn- -check-operator [op clause deltas]
  "Throws an error when op isn't add or subtract"
  (when (not (#{:add :subtract} op))
    (throw (ex-info (str "Delta clause "
                         clause
                         " needs an appropriate operator")
                    {:type ::bad-delta-clause
                     :clause clause
                     :deltas deltas
                     }))))


^:reduce-fn
(defn collect-delta-clause [model bmap deltas clause]
  "conjoins clause with vars mapped to bindings in bmap
Only adds and subtracts if the current state of the model justifies it."
  (letfn [(resolve-var [bmap elt]
            ;; swaps in a binding for elt
            ;; if it's in bmap to variables
            (or (bmap elt)
                elt))
          ]
    (let [[op s p o] (into []
                           (map
                            (partial resolve-var bmap) clause))]
      (timbre/debug "After resolving vars: " [op s p o])
      (assert (not (fn? s)))
      (-check-operator op clause deltas)
      (if (model s p o)
        ;; assert subtracts but not adds
        (if (= op :subtract)
          (conj deltas [:subtract s p o])
          deltas)
        ;; else not in model
        ;; assert adds but not subtracts
        (if (= op :add)
          (conj deltas [:add s p o])
          deltas)))))

^:reduce-fn
(defn- -collect-consequents [model rules deltas match-spex]
  "Returns [<delta>, ...] appropriate for `match-spex` applied to <consequent> of some <rule> in `rules`, applied to `model`
Where
<delta> := [<op> <value> <value> <value>], 
  'add' deltas will only be included if the triple is absent
  'subtract' deltas will only be included if the triple is present
<match-spex> := {:rule ..., :bindings ...}
<consequent> := A graph pattern applicable to a <bmap> to produce 
  [<delta>, ...], e.g. [[:add :?myVar :isa :?myClass]]. This may be
  informed by a :infer/specialBinding specification where new identifiers need
  to be created.
  Alternatively, this could be := (fn [deltas model bmap] -> <deltas'>
<rule> names a rule in <rules>, s.t. {<rule> <rule-desc>, ...}
  it will have :infer/consequent and may have :infer/specialBinding
  Also, individual values of any <var> may 
<rules> Is an IGraph describing a set of rules using the Rules Ontology
  applicable to <model>
<rule-desc> := {:infer/antecedent...
                :infer/consequent...
                :infer/specialBinding... (optional)
                <var> <value>... (optional)
               }
<op> :~ #{:add :subtract}
<value> is a graph element in <model>
<bindings> := [<bmap>, ...]
<model> is the IGraph to which <rules> is being applied, and which
  already contains the triple in <delta>
<bmap> := {<var> <value>, ...}, a binding to the <antecedent> of <rule>
<antecedent> = (the (rules <rule> :infer/antecedent))
<var> is a :?variable in <antecedent> an/or <consequent> 
"
  (let [rule (:rule match-spex)
        ]

    (log :log/StartConsequents :log/ruleID rule)
    (letfn [(collect-special [antecedent-bmap _var]
              ;; binds _var to (f model antecedent-bmap)
              ;; called after antecedent and before consequent
              (timbre/debug "collecting special " antecedent-bmap "/" _var)
              (let [f (the (rules rule _var))]
                (assert f)
                (log :log/TempAboutToAssocAntecentBmap
                     :log/f f
                     :log/var _var
                     :log/bmap antecedent-bmap)
                (assoc antecedent-bmap _var
                       (f model antecedent-bmap))))

            (functional-consequent [rules rule]
              ;; non-nil if the consequent is a fn [model deltas antecedent-bmap]
              (let [fn-bindings (query rules
                                       [[rule :infer/consequentFn :?fnId]
                                        [:?fnId :igraph/compiledAs :?fn]])]
                (if-let [fn-binding (the fn-bindings)]
                  (:?fn fn-binding))))
              
            (collect-bindings [deltas antecedent-bmap]
              ;; appends consequents of rule, mapping bindings in antecedent-bmap
              ;; possibly setting a special binding
              (let [antecedent-bmap (reduce collect-special
                                            antecedent-bmap
                                            (the (rules
                                                  rule
                                                  :infer/specialBindings)))]
                (if-let [f (functional-consequent rules rule)]
                  (f rules model deltas antecedent-bmap)
                  ;; else it's standard deltas
                  (reduce (partial collect-delta-clause model antecedent-bmap)
                          deltas
                          (local-bindings rules rule :infer/consequent)))))
             ]
      (let [bindings (reduce collect-bindings deltas (:bindings match-spex))]
        (if (empty? bindings)
          (log :log/EmptyConsequentBindings :log/ruleID rule)
          ;;else
          (log :log/GotConsequentBindings
               :log/ruleID rule
               :log/bindings bindings))
        bindings))))


(defn maybe-derive [s-p-o]
  "Side-effect: derives <s> from <o> if (isa? p :igraph/subsumedBy)"
  (let [[s p o] s-p-o]
    (when (and (isa? p :igraph/subsumedBy)
               (not (isa? s o)))
      (derive s o))
    [s p o]
    ))

(defn maybe-underive [s-p-o]
  "Side-effect: derives <s> from <o> if (isa? p :igraph/subsumedBy)"
  (let [[s p o] s-p-o]
    (when (isa? p :igraph/subsumedBy)
      (underive s o))
    [s p o]
    ))

(defn incorporate-delta [model [op s p o]]
  "Returns `model`', modified per <op> <s> <p> <o>
Where
<op> :~ #{:add :subtract}
<s> <p> <o> are graph elements to be added/removed from <model>
"
  (timbre/debug "Incorporating delta " [op s p o])
  (if (and (= op :add) (not (model s p o)))
    (add model (maybe-derive [s p o]))
    ;;else
    (if (and (= op :subtract) (model s p o))
      (subtract model (maybe-underive [s p o]))
      ;; else
      model)))

(defn apply-rules [model context]
  "Returns [context, [<delta>, ...]] appropriate for `model` in `context`
Where
<context> := {:rules... :index... :visited-values... , :match-history...}
<delta> := [<op> <value> <value> <value>], 
  'add' deltas will only be included if the triple is absent
  'subtract' deltas will only be included if the triple is present
<model> is the IGraph to which <rules> is being applied, and which
  already contains the triple in <delta>
<op> :~ #{:add :subtract}
<value> is a graph element in <model> 
<rules> Is an IGraph describing a set of rules using the Rules Ontology
  applicable to <model>, informing a set of <match-spex>
<index> := {<value> [<rule>, ...]}
<visited-values> := #{<value>, ...}, encountered during a traversal
  presumed to have just finished the normal implication gather stage
<match-spex> := {:rule ..., :bindings ...}
<match-history> := {<rule> [<previous-binding>, ...] , ...}
  Used to filter bindings from new matches.

<rule> names a rule in <rules>, s.t. {<rule> <rule-desc>, ...}
  it will have :infer/consequent and may have :infer/specialBinding
  Also, individual values of any <var> may 
<rule-desc> := {:infer/antecedent...
                :infer/consequent...
                :infer/specialBinding... (optional)
                <var> <value>... (optional)
               }
<bindings> := [<bmap>, ...]
<antecedent> = (the (rules <rule> :infer/antecedent))
<consequent> := A graph pattern applicable to a <bmap> to produce 
  [<delta>, ...], e.g. [[:add :?myVar :isa :?myClass]]. This may be
  informed by a :infer/specialBinding specification where new identifiers need
  to be created.
<bmap> := {<var> <value>, ...}, a binding to the <antecedent> of <rule>
<clause> := [<elt> <elt> <elt>]
<elt> is a ?:var or a literal
<consequent-spec> is a <delta> specification with :?vars
"
  {:pre [(:rules context)]
   }
  (let [[context, match-spex] (get-matches model context)
        ;;matches (get-matches model context)
        deltas (reduce (partial -collect-consequents
                                model
                                (:rules context))
                       []
                       match-spex)
        ]
    [context, deltas]))

(defn apply-localized-rules [rules model local-bindings]
  "Returns [<delta>, ...] applying `local-bindings` from `model` to `rules`
Where
<delta> := [<op> <s> <p> <o>]
<local-bindings> := {<rule-id> {<var> <value, ...}}
<model> implements IGraph, representing application state
<rules> implements IGraph, representing rules that inform the effective ontology
<rule-id> names a rule in <rules>, some of whose <var>s will be bound to <val>s.
<var> is a variable referenced in <rule>
<value> is a local binding for <var> 
"
  (letfn [(get-deltas [[context deltas]] deltas)
          (collect-local-rule-bindings [rule-id rules _var _val]
            (add rules [rule-id _var _val]))
          (collect-rule-bindings [rules rule-id var-val]
            (reduce-kv (partial collect-local-rule-bindings rule-id)
                       rules
                       var-val))
          (localize [rules]
            (reduce-kv collect-rule-bindings rules local-bindings))
          ]
    (get-deltas
     (apply-rules model
                  {:rules (localize rules)
                   :rule-candidates
                   (fn [context]
                     (set (keys local-bindings)))
                   }))))


(declare infer-implications)

(defn apply-rules* [model context]
  "Returns `model`', modified per rules specified in `context`
Where
<model> is an IGraph
<model>' has additions/subtractions implied by <rules>
<context> := {:rules... :index... :visited-values... , :match-history...}
<rules> is an IGraph encoding rules in the rules ontology
<index> is created by ??? to optimize access to rules resources
<match-history> := {:rule... :bindings...}, for rules applied in the
  course of traversal
<rule> names a rule in <rules>
<bindings> := {<var> <value>, ...} querying the antecedent of <rule> against
  <model>
"
  (loop [g model c context]
    (let [[c deltas] (apply-rules g c)
          ]
      (def ^:dynamic *model-in-apply-rules* g)
      (def ^:dynamic *diff-in-apply-rules* (difference g model))    
      (if (empty? deltas)
        g
        (recur (infer-implications g deltas)
               c)))))

(defn match-only [rules-model model rule-id]
  "Returns matches for <rule-id> against model"
  (let [[context matches]
        (get-matches model
               {:rules rules-model
                :rule-candidates (fn [context] #{rule-id})
                })]
    matches))
               
(defn apply-only [rules-model model rule-id]
  "Returns `model`', modified per `rule-id` in `rules-model`"
  (apply-rules* model
                {:rules rules-model
                 :rule-candidates (fn [context] #{rule-id})
                 }))


(defn apply-localized-rules-to-model [rules rule-appendix model]
  "Returns `model`, modified by the <rule-id>s in `rule-appendix`, which modifies  `rules` with localized bindings before they are applied.
Where
<model> is an IGraph to which <rules> are applicable
<rules> is an IGraph informed by the rules ontology
<rule-appendix> := [<rule-modification>, ...]
<rule-modification> := [<rule-id> :?var :?value, ...]
<rule-id> identifies a rule specified in <rules>, with an <antecedent>
<?var> is a variable cited in <antecedent>
<value> is a specific value to be bound to :?var in advance of matching 
  the rule against <model>. This makes <rule> more specific and should
  speed its execution.
NOTE: Only the rules specified <rule-appendix> will be applied, and they
  will be applied in the order that they occur in the appendix.
"
  (reduce (partial apply-only (add rules rule-appendix))
          model
          (map first rule-appendix)))


;; IMPLICATIONS MULTIMETHOD


(defn implications-dispatch [model context op s p o]
  "Returns [<op> <s> <p> <o>], used to dispatch implications
Where
<op> :~#{:add subtract}
<s> <p> <o> :~ {<self> :kwi :set :map :vector :number :graph <type>}
"
  (assert #{:add :subtract} op)
  (let [result
        [op
         (if (parents s)
           s
           (let []
             (assert (keyword? s))
             :rdf/Resource))
         p 
         (if (parents o)
           o
           ;; Else we map type to a simple keyword name
           (or (the (model o :proto/elaborates))
               (cond
                 (set? o) :set
                 (map? o) :map
                 (vector? o) :vector
                 (number? o) :number
                 (keyword? o) :rdf/Resource
                 (instance? (type empty-graph) o) :graph
                 :default (type o))))
         ]]
    (timbre/debug "Implications dispatch on " [op s p o] ":" result)
    result))


(defmulti implications
  "Given [model context op s p o], returns [<delta>, ...] appropriate to `model` and `context`. Dispatched on [op s p o].
  Where
  <model> is an IGraph
  <context> is a traversal context := {:rules... :index..., ...}
  <op> is in #{:add :subtract}, 
  <s> <p> <o> is a recently acquired or deleted triple (indicated by <op>)
  <delta> := [<op> <s> <p> <o>], a change implied by the incoming args
  NOTE: this is used to provide 'hooks' to respond to changes in the model.
  "
  implications-dispatch)

(defmethod implications :default 
  [model context op s p o]
  (let [dispatch (implications-dispatch model context op s p o)
        ]
    (log :log/DefaultImplications
         :log/rawDelta [op s p o]
         :log/dispatch dispatch)
    ;; no deltas
    []))

^:traversal-fn
(defn implications* [_ context model deltas]
  "A traversal function. Returns [`context`, `model`', `deltas`'] incorporating the current deltas queue into the model, and producing a new batch of deltas implied by the incoming set as process of forward-chaining.
Where
<model> is an igraph
<deltas> := [<delta>, ...], the initial traversal queue
<delta> := [<op> <s> <p> <o>]
<op> is one of #{:add :subtract}
(implications <model> <op> <s> <p> <o>) ->[ <to-subtract> <to-add>]
<model'> subtracts <to-subtract> and adds <to-add> to <model>
<deltas'> is the rest of <deltas> plus any members of <to-add>
<context> is used by the traverse function to avoid cycles
"
  
  (letfn [(collect-implications [model implied-deltas [op s p o]]
            (reduce conj
                    implied-deltas
                    (implications model context op s p o)))
          ;; since we're taking on batches of deltas, we have
          ;; assume some of the usual work of the traverse function...
          (qualified? [delta]
            (not (contains? (:history context) delta)))
          ]
    (let [deltas (filter qualified? deltas)
          model (reduce incorporate-delta
                        model
                        deltas)
          ]
      (timbre/debug "TEMP: deltas in implications*: " (into [] deltas))
      [(assoc context
              :history (reduce conj
                               (:history context)
                               deltas))
       ,
       model
       ,
       (reduce (partial collect-implications model) [] deltas)
       ])))


(defn infer-implications [model deltas]
  "Returns `model`' incorporating all implications inferable from `deltas`
Where
<model> is a graph of the current goal
<deltas> := [<delta>, ...]
<delta> := [<op> <s> <p> <o>], a triple to add/subtract from <model>"
  (traverse model
            implications* ;; traversal fn
            model ;; accumlator 
            deltas ;; queue
            ))

;;;;;;;;;;;;;;;;;;
;; DIAGNOSTICS
;;;;;;;;;;;;;;;;;;
    
(defn diagnose-matches
  "Returns [<bmap>, ...] for `partial` version of state  in `log-entry`
  Where
  <bmap> is a binding to <partial rule>
  <partial> is <n> or :special
    <n>  will match the first <n> clauses in (:log/antecedent log-entry)
    :special will match the whole antecedent and acquire special bindings
  <log-entry> supports the following vocabulary:
    :log/antecedent
    :log/rules
    :log/ruleID
    :log/model
    :log/bmaps
    :log/locally-bound
  "
  ([log-entry-id]
   (diagnose-matches @log-graph log-entry-id nil))

  ([log-entry-id partial]
   (diagnose-matches @log-graph log-entry-id partial))
  
  ([g log-entry-id partial]
   (let [context (the (g log-entry-id :log/context))
         rules (:rules context)
         rule-id (the (g log-entry-id :log/ruleID))
         antecedent (the (g log-entry-id :log/antecedent))
         partial (or partial (count antecedent))
         ]
   (letfn [(match-partial-antecedent [n]
             (let [antecedent' (subvec antecedent 0 n)
                   [c matches]
                   (get-matches
                    (the (g log-entry-id :log/model))
                    (assoc (dissoc context :match-history)
                           :rules (add (subtract rules
                                                 [rule-id :infer/antecedent])
                                       [rule-id :infer/antecedent antecedent'])))
                   ]
               (assoc (the matches) :antecedent antecedent')
               #_(assoc matches :antecedent antecedent')))
           ]
     (let [original-log @log-graph]
       (try
         (let []
           (log-reset! initial-log-graph)
           (if (int? partial)
             (match-partial-antecedent
              (min (count antecedent) partial))
             (throw (ex-info "Special Not yet supported" {:type :NotYetSpecified}))
             ;;(match-special-bindings)
             ))
         (finally (reset! log-graph original-log)))
  
       )))))
