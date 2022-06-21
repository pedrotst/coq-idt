From idt Require Import all.
From MetaCoq.Template Require Import utils All.

Notation "'unfolded' d" :=
  ltac:(let y := eval unfold d in d in exact y) (at level 100, only parsing).



Inductive llist (A : Set) : Set :=
| nill  : llist A
| conss : A -> llist A -> llist A.

Arguments nil {A}.
Arguments conss {A} _ _.

(* Notation type_of' t := (Type -> (_ : TypeOf t)) (only parsing). *)

(* Polymorphic Definition newlistT@{i j} := forall (A: Type@{i}) (X : Type@{j}), Type@{max(i, j)}. *)
(* Axiom F : forall (A B C D: Set), Set. *)


Inductive tree (A : Set) : Set :=
| mepty : tree A
| node : A -> tree A -> tree A -> tree A
.

Notation T := list.

Definition newT : Type.
  let rec go x :=
    match x with
        | forall (A :?Z), ?M =>  refine (forall (A : Z), _); go M
        | ?U => exact (forall (X : Set), U)
    end in
  let Ty := type of T in
  go Ty.
Defined.

(* Set Printing All. *)
(* MetaCoq Test Quote (forall (A: Set) (X : Set), Set). *)

MetaCoq Run (l <- tmEval (unfold (MPfile ["list"], "newT")) newT;;
             l' <- tmQuote l;;
             tmPrint l').


(* Definition newlistT := forall (A: Set) (X : Set), Set. *)

Definition newlist : tsf_ctors_ty (newT).
Proof.


  run_template_program (get_ctors T)
                       (fun xs =>
                          let xs := eval simpl in xs in
                          let rec go xs :=
                            lazymatch xs with
                            | (?name, (existT_typed_term ?cty ?ctor)) :: ?xs =>
                                let n := eval compute in (append name "F") in
                                refine ((n, _) :: _); [
                                  intros Hc R; unfold newT in R; tsf_interact ctor R
                                | go xs ]
                            | _ => exact []
                            end
                          in go xs).
  (* tsf_ctors llist (fun X => append X "F") tsf_interact. *)

  -
    let rec rector ty := match ty with
                             | forall (A : Set), ?U => refine (forall (A : Set), _);
                                                 try specialize (ctor A);
                                                 pose proof R A as R;
                                                 rector U
                             | _ => idtac
                         end in
    let Ty := type of R in
    rector Ty.

    let rec go' ty := match ty with
                          | T A -> ?U =>
                              refine (X ->  _); go' U
                          | forall A : ?S, ?U =>
                              refine (forall (A : S), _); go' U
                          | T A => exact R
                      end in
    let Ty := type of ctor in
    go' Ty.
    Show Proof.

  -
    let rec rector ty := match ty with
                             | forall (A : Set), ?U => refine (forall (A : Set), _);
                                                 try specialize (ctor A);
                                                 pose proof R A as R;
                                                 rector U
                             | _ => idtac
                         end in
    let Ty := type of R in
    (* idtac R. *)
    rector Ty.



    let rec go' ty := lazymatch ty with
                          | T A -> ?U =>
                              refine (X ->  _); go' U
                          | forall B0 : ?T0, ?U =>
                              refine (forall (B0 : T0), _); go' U
                          | T A =>
                              (* exact (R A X) *)
                              exact R
                      end in
    let Ty := type of ctor in
    go' Ty.
    Show Proof.
Defined.

(* Set Printing Universes. *)

(* Eval unfold newlist in newlist. *)

(* MetaCoq Run (l <- tmEval all *)
                        (* (unfold (MPfile ["list"], "newlist")) *)
             (*            newlist;; *)
             (* l' <- tmQuote l;; *)
             (* tmPrint l'). *)
(* Eval unfold newlist in ltac:(tsf_ctors_to_tm newlist). *)
Arguments newlist /.

(* [("nillF", fun R : Type -> Type -> Type => forall A X : Type, R A X); *)
(* ("conssF", fun R : Type -> Type -> Type => forall A X : Type, A -> X -> R A X)] *)

(* Inductive _listF (A : Set) (X : Set) : Set := *)
(* | _nilF : _listF A X *)
(* | _consF : A -> X -> _listF A X. *)


(* MetaCoq Quote Recursively Definition _listF_syntax := _listF. *)
(* MetaCoq Quote Recursively Definition _llist_syntax := llist. *)

(* Eval compute in (tSort (Universe.of_levels (inr (Level.Level "list.172")))). *)
(* Eval compute in (Universe.from_kernel_repr *)
(*                                           (Level.lSet, false)). *)
                                          (* [(Level.Level "list.218", false); *)
                                          (* (Level.Level "list.219", false)]). *)

(*

{|
ind_finite := Finite;
ind_npars := 2;
ind_params := [{|
               decl_name := {| binder_name := nNamed "A"; binder_relevance := Relevant |};
               decl_body := None;
               decl_type := tSort
                              {|
                              Universe.t_set := {|
                                                UnivExprSet.this := [(Level.lSet, 0)];
                                                UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                              (Level.lSet, 0) |};
                              Universe.t_ne := eq_refl |} |};
              {|
              decl_name := {| binder_name := nNamed "X"; binder_relevance := Relevant |};
              decl_body := None;
              decl_type := tSort
                             {|
                             Universe.t_set := {|
                                               UnivExprSet.this := [(Level.lSet, 0)];
                                               UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                              (Level.lSet, 0) |};
                             Universe.t_ne := eq_refl |} |}];
ind_bodies := [{|
               ind_name := "listF";
               ind_type := tProd
                             {| binder_name := nNamed "A"; binder_relevance := Relevant |}
                             (tSort
                                {|
                                Universe.t_set := {|
                                                  UnivExprSet.this := [(Level.lSet, 0)];
                                                  UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                              (Level.lSet, 0) |};
                                Universe.t_ne := eq_refl |})
                             (tProd
                                {|
                                binder_name := nNamed "X";
                                binder_relevance := Relevant |}
                                (tSort
                                   {|
                                   Universe.t_set := {|
                                                     UnivExprSet.this := [(Level.lSet, 0)];
                                                     UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                              (Level.lSet, 0) |};
                                   Universe.t_ne := eq_refl |})
                                (tSort
                                   {|
                                   Universe.t_set := {|
                                                     UnivExprSet.this := [(Level.lSet, 0)];
                                                     UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                              (Level.lSet, 0) |};
                                   Universe.t_ne := eq_refl |}));
               ind_kelim := IntoAny;
               ind_ctors := [("nillF",
                             tProd
                               {|
                               binder_name := nNamed "A";
                               binder_relevance := Relevant |}
                               (tSort
                                  {|
                                  Universe.t_set := {|
                                                    UnivExprSet.this := [(Level.lSet, 0)];
                                                    UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                              (Level.lSet, 0) |};
                                  Universe.t_ne := eq_refl |})
                               (tProd
                                  {|
                                  binder_name := nNamed "X";
                                  binder_relevance := Relevant |}
                                  (tSort
                                     {|
                                     Universe.t_set := {|
                                                       UnivExprSet.this := [(Level.lSet, 0)];
                                                       UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                              (Level.lSet, 0) |};
                                     Universe.t_ne := eq_refl |})
                                  (tProd
                                     {|
                                     binder_name := nNamed "A";
                                     binder_relevance := Relevant |}
                                     (tSort
                                        {|
                                        Universe.t_set := {|
                                                          UnivExprSet.this := [(Level.lSet,
                                                              0)];
                                                          UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                              (Level.lSet, 0) |};
                                        Universe.t_ne := eq_refl |})
                                     (tProd
                                        {|
                                        binder_name := nNamed "X";
                                        binder_relevance := Relevant |}
                                        (tSort
                                           {|
                                           Universe.t_set := {|
                                                             UnivExprSet.this := [(Level.lSet,
                                                              0)];
                                                             UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                              (Level.lSet, 0) |};
                                           Universe.t_ne := eq_refl |})
                                        (tSort
                                           {|
                                           Universe.t_set := {|
                                                             UnivExprSet.this := [(Level.lSet,
                                                              0)];
                                                             UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                              (Level.lSet, 0) |};
                                           Universe.t_ne := eq_refl |})))), 2);
                            ("conssF",
                            tProd
                              {| binder_name := nNamed "A"; binder_relevance := Relevant |}
                              (tSort
                                 {|
                                 Universe.t_set := {|
                                                   UnivExprSet.this := [(Level.lSet, 0)];
                                                   UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                              (Level.lSet, 0) |};
                                 Universe.t_ne := eq_refl |})
                              (tProd
                                 {|
                                 binder_name := nNamed "X";
                                 binder_relevance := Relevant |}
                                 (tSort
                                    {|
                                    Universe.t_set := {|
                                                      UnivExprSet.this := [(Level.lSet, 0)];
                                                      UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                              (Level.lSet, 0) |};
                                    Universe.t_ne := eq_refl |})
                                 (tProd
                                    {|
                                    binder_name := nNamed "A";
                                    binder_relevance := Relevant |}
                                    (tSort
                                       {|
                                       Universe.t_set := {|
                                                         UnivExprSet.this := [(Level.lSet,
                                                              0)];
                                                         UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                              (Level.lSet, 0) |};
                                       Universe.t_ne := eq_refl |})
                                    (tProd
                                       {|
                                       binder_name := nNamed "X";
                                       binder_relevance := Relevant |}
                                       (tSort
                                          {|
                                          Universe.t_set := {|
                                                            UnivExprSet.this := [(Level.lSet,
                                                              0)];
                                                            UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                              (Level.lSet, 0) |};
                                          Universe.t_ne := eq_refl |})
                                       (tSort
                                          {|
                                          Universe.t_set := {|
                                                            UnivExprSet.this := [(Level.lSet,
                                                              0)];
                                                            UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok
                                                              (Level.lSet, 0) |};
                                          Universe.t_ne := eq_refl |})))), 2)];
               ind_projs := [];
               ind_relevance := Relevant |}];
ind_universes := Monomorphic_ctx
                   ({|
                    VSet.this := [Level.lSet];
                    VSet.is_ok := LevelSet.Raw.add_ok (s:=[Level.lSet]) Level.lSet
                                    (LevelSet.Raw.add_ok (s:=[Level.lSet]) Level.lSet
                                       (LevelSet.Raw.add_ok (s:=[]) Level.lSet
                                          LevelSet.Raw.empty_ok)) |},
                   {| CS.this := []; CS.is_ok := ConstraintSet.Raw.empty_ok |});
ind_variance := None |}
*)
(* Unset Strict Unquote Universe Mode. *)
(* Fail MetaCoq Unquote Definition t1 := (tSort (Universe.make (Level.Level "List.232"))). *)

(* MetaCoq Unquote Definition t2 := (tSort fresh_universe). *)
(* MetaCoq Unquote Definition t3 := (tSort (Universe.make (Level.Level "Top.400"))). *)

(* Definition xParam univ : context_decl := *)
(*   {| decl_name := {| binder_name := nNamed "X"; *)
(*                     binder_relevance := Relevant |}; *)
(*     decl_body := None; *)
(*     decl_type := tSort univ |}. *)

    (* ind_params := [{| *)
    (*                decl_name := {| *)
    (*                             binder_name := nNamed "A"; *)
    (*                             binder_relevance := Relevant |}; *)
    (*                decl_body := None; *)
    (*                decl_type := tSort (Universe.of_levels (inr (Level.Level "list.214"))) |}]; *)

  (* { decl_name : aname;  decl_body : option term;  decl_type : term } *)

(* Ltac ctor_types ctors := let rec go xs := *)
(*                            lazymatch xs with *)
(*                                | (?n, ?ctor) :: ?xs => *)
(*                                    lazymatch ctor with *)
(*                                        | (fun _ => ?P) => *)
(*                                            lazymatch P with *)
(*                                                | (fun _ => tsf_skip_marker) => idtac *)
(*                                                | _ => refine ((n, P) :: _) *)
(*                                            end *)
(*                                    end; go xs *)
(*                                | _ => refine ([]) *)
(*                            end in *)
(*                          let xs := eval cbn in newlist *)
(*                            in go xs. *)


Fixpoint extract_params (t : term) (n : nat) : list (aname * term) :=
  match n with
      | O => []
      | S n' => match t with
                   | tProd s ty t' => (s, ty) :: extract_params t' n'
                   | _ => []
               end
  end.

Fixpoint extract_ty_ret (t : term) : term :=
  match t with
      | tProd _ _ t' => extract_ty_ret t'
      | t => t
  end.

Definition mk_indparam (s : aname) (t : term) : context_decl :=
  {| decl_name := s;
    decl_body := None;
    decl_type := t |}.


Definition c := tSort (Universe.of_levels (inr (Level.Level "list.214"))).
Eval compute in c.

Definition get_level (t : term) : list LevelSet.elt :=
  match t with
      | tSort (Universe.lType {|Universe.t_set := {| UnivExprSet.this := xs |}
              |}) => map fst xs
      | _ => []
  end.

Fixpoint count_tProds' (n : nat)  (t : term) : nat :=
  match t with
      | tProd _ _ t' => count_tProds' (S n) t'
      | _ => n
  end.

Definition count_tProds := count_tProds' 0.


#[universes(polymorphic)]
Definition ind_gen' (name : ident) (ctors : list (ident * term))
           (mind : mutual_inductive_body) (i : nat) : TemplateMonad unit :=
  (* let new_univ := fresh_universe in *)
  (* t <- tmEval (unfold (MPfile ["list"], "newlistT"))  newlistT;; *)
  ty <- tmQuote (unfolded newT) ;;
  match nth_error mind.(ind_bodies) i with
  | Some ind =>
      let npars := mind.(ind_npars) + 1 in
      let ctors := map (fun '(n, t) =>
                          let t' := try_remove_n_lambdas 1 t in
                          (n, t', count_tProds t' - npars)) ctors in
      let params := extract_params ty npars in
      let ty_ret := extract_ty_ret ty in
      let indparam := map (fun '(s, t) => mk_indparam s t) params in
      let param_terms := map snd params in
      let lvls := flat_map get_level (ty_ret :: param_terms) in
      (* let univ := Monomorphic_ctx (LevelSetProp.of_list lvls, ConstraintSet.empty) in *)
      let univ := Monomorphic_ctx (LevelSetProp.of_list [], ConstraintSet.empty) in
      let ind' :=
        {| ind_finite := mind.(ind_finite);
           ind_npars := mind.(ind_npars) + 1;
           (* ind_universes := mind.(ind_universes); *)
           ind_universes := univ;
           ind_variance := mind.(ind_variance);
           (* ind_params := mind.(ind_params) ++ [xParam new_univ]; *)
           ind_params := indparam;
           ind_bodies := [ {| ind_name := name;
                              ind_type  := ty;
                              ind_kelim := ind.(ind_kelim);
                              ind_ctors := ctors;
                              ind_projs := ind.(ind_projs);
                              ind_relevance := ind.(ind_relevance) |} ]
        |}
      in
      (* ind'' <- tmEval all ind';; *)
      (* tmPrint ind'';; *)
      tmMkInductive' ind'
  | _ => tmFail "No body found"
  end.


MetaCoq Run (
          (* l <- tmQuote llist;; *)
          '(mind, i) <- tsf_get_mind ltac:(quote_term T (fun t => exact t));;
          (* let ctors := ltac:(ctor_types newlist) in *)
          let ctorsT := ltac:(tsf_ctors_to_tm newlist) in
          (* tmPrint ctors;; *)
          (* tmPrint mind ;; *)
          ind_gen' "treeF" ctorsT mind i

          (* tsf_ind_gen_from llist "listF" newlist *)
        ).


    
  

MetaCoq Run
        (tm <- tmQuote llist;;
         (* tmPrint tm). *)
         c <- match tm with
             | tInd ({|inductive_mind := mind; inductive_ind := i |} as ind) _ =>
                 q_mind <- tmQuoteInductive mind;;
                 (* tmPrint ind;; *)
                 (* tmPrint q_mind;; *)
                 match nth_error q_mind.(ind_bodies) i with
                 | Some {| ind_ctors := ((name, ctor, _) :: ctors) |} =>

                     let tm := (tConstruct ind 0 []) in
                     let tm2 := (tConstruct ind 1 []) in
                     (* tmPrint ctor;; *)
                     ct1 <- tmUnquote tm;;
                     ct2 <- tmUnquote tm2;;
                     c1 <- tmEval (unfold (Common_kn "my_projT1")) (my_projT1 ct1) ;;
                     c2 <- tmEval (unfold (Common_kn "my_projT1")) (my_projT1 ct2) ;;
                     (* let x1 : Type := c1 in let x2 : Type := c2 in *)
                     (* tmReturn (conss c1 (conss c2 nill)) *)
                     tmReturn [c1 ; c2]
                     (* tmReturn tt *)
                     (* monad_map_i (fun i '(name, ctor, _) => *)
                     (*                let tm := (tConstruct ind i []) in *)
                     (*              (* tmPrint ctor;; *) *)
                     (*              ct <- tmUnquote tm;; *)
                     (*              ct1 <- tmEval (unfold (Common_kn "my_projT1")) (my_projT1 ct) ;; *)
                     (*              ct2 <- tmEval (unfold (Common_kn "my_projT2")) (my_projT2 ct) ;; *)
                     (*              tmPrint ct ;; *)
                     (*              tmPrint ct1 ;; *)
                     (*              tmPrint ct2 ;; *)
                     (*              ret (name, ct) *)
                     (*              (* ret tt *) *)
                     (*           ) *)
                     (*           ctors *)
                 (* tm <- tmUnquote  *)
                 (* monad_map_i (fun i '(name, ctor, _) => *)
                 (*                tm <- tmUnquote ctor;; *)
                 (*                       (* (tConstruct ind i []);; *) *)
                 (*                ret (name, tm)) *)
                 (*             ctors *)
                 | _ => tmFail "No body found"
                 end
             | _ => tmFail "Not an inductive type"
             end ;;
         tmPrint c

        ).

Definition x1 := forall A : Type, list A.
Definition x2 := forall A : Type, A -> list A -> list A.
Definition l := [x1 ; x2].

        (* (ctors <- get_ctors (fun X => list X);; *)
        (*  tmPrint ctors). *)

Eval compute in x.
