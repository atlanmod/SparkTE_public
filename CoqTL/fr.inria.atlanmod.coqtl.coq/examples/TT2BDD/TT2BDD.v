Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.Utils.

Require Import core.ConcreteSyntax.
Require Import core.Semantics.
Require Import core.Metamodel.
Require Import core.Expressions.

Require Import TT2BDD.TT.
Require Import TT2BDD.BDDv2.

Open Scope coqtl.

Definition TT2BDD :=
    transformation TTMetamodel bddMetamodel [
        (* The TruthTable transforms to a BDD, with the same name and Ports. *)
        rule "TT2BDD" 
        from [LocatedElementEClass]
        to [
            elem [LocatedElementEClass] BDDEClass "bdd"
            (fun i m t => (* (BuildBDD (TruthTable_getId t) (TruthTable_getName t)) *)
             match (TTMetamodel_LocatedElement_DownCast TruthTableEClass t) with 
             | Some tr => (BuildBDD (LocatedElement_getId t) (TruthTable_getName tr))
             | None => (BuildBDD (LocatedElement_getId t) "")
             end)
            nil
        ]

        (* Each InputPort transforms to an InputPort, with the same name. *)

        (* Each OutputPort transforms to an OutputPort, with the same name. *)
     
        (* Each Cell for the OutputPorts transform into Assignments. *)
     
        (* Each Row transforms to a Leaf. *)
     
        (* The TruthTable transforms into a subtree for each combination of input values, each subtree is owned by the subtree with iterator = i/2  *)
     
    ].


(* We want to prove the following equivalence: 
   given an assignment for all input ports 'ins', and given an output port 'out', 
   (valueOf (evalTT TT ins) out) = (valueOf (evalBDD BDD ins) out) *)

Close Scope coqtl.