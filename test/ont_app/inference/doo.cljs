(ns ont-app.inference.doo
  (:require [doo.runner :refer-macros [doo-tests]]
            [ont-app.inference.core-test]
            ))

(doo-tests
 'ont-app.inference.core-test
 )
