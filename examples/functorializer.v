From idt Require Import all.
From MetaCoq.Template Require Import utils All.

(* This file converts a datatype to it's functorial representation *)
(* Following the logic of dc-recursion/.../List.v *)

(* We start by defining the datatype that we want make the convertion *)
(* This way we can avoid any issues with universes and whatnot *)
(* Also notice that so far we work solely with Sets, working with Type is future work *)

Inductive list' (A : Set) : Set :=
| nil'  : list' A
| cons' : A
 -> list' A -> list' A.

(* Arguments nil' {A}. *)
(* Arguments cons' {A} _ _. *)

Inductive tree (A B : Set) : Set :=
| mempty : tree A B
| mnode : A -> B -> tree A B -> tree A B -> tree A B.

(* TODO: The Name X for parameters is currently unavailable *)

(* ------- EDIT here ------ *)

(* Type being Functorialized *)
Notation T := tree.
(* Functor Name *)
Notation Fname := "treeF".

Reserved Notation "'x" (at level 100).

(* ------------------------ *)

(* To transform the datatype to it's functorial representation *)
(* The first step is to add (X : Set) as it's last parameter *)
(* X will be used as the "recursive call" of the datatype *)
Definition newT : Type.
  let rec go x :=
    match x with
        | forall (A :?Z), ?M =>  refine (forall (A : Z), _); go M
        (* Adds X as the last parameter *)
        | ?U => exact (forall (X : Set), U)
    end in
  let Ty := type of T in
  go Ty.
Defined.

(* Now we are going to edit the type of each constructor *)
(* Following the same strategy as in `tutorial.v` *)
Definition newT_ctors : tsf_ctors_ty (newT).
Proof.

  (* We introduce the signature of the datatype as R, *)
  (* and each one of it's constructor to the context  *)

  tsf_ctors T (fun s => append s "F") tsf_interact; unfold newT in R.


  all: unfold newT in R.
  (* Now we refine each one of R parameters with `refine (forall A, _)` *)
  (* And apply each one to R, to build it's complete return type for each constructor *)
  all:
    let rec rector ty := match ty with
                             | forall (A : Set), ?U => refine (forall (A : Set), _);
                                                 try specialize (ctor A);
                                                 pose proof R A as R;
                                                 rector U
                             | _ => idtac
                         end in
    let Ty := type of R in
    rector Ty.

  all:
    (* This function gets the return type of a constructor *)
    let rec ctorTy ty := match ty with
                             | forall (_ : _), ?U => ctorTy U
                             | ?U => U
                         end in
    let Ty := type of ctor in
    (* We remember the type of the constructor as Cty *)
    let Cty := ctorTy Ty in
    (* Finally, to functorialize each constructor do the following: *)
    let rec go' ty := match ty with
                        (* If Cty appears as a type, change it to X *)
                          | Cty -> ?U => refine (X ->  _); go' U
                          | forall (A : Cty), ?U => refine (forall (A : X), _); go' U
                          (* Everything else remains unchanged *)
                          | ?S -> ?U => refine (S -> _); go' U
                          | forall A : ?S, ?U => refine (forall (A : S), _); go' U
                          (* If Cty appears as the return type, change it to R *)
                          | Cty => exact R
                          (* TODO: Add other cases for more complex datatypes *)
                      end in
    go' Ty.
Defined.

Arguments newT_ctors /.

(* ------------ Metacoq Auxiliary Functions ------------ *)

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

Notation "'unfolded' d" :=
  ltac:(let y := eval unfold d in d in exact y) (at level 100, only parsing).

(* ----------------------------------------------------- *)

(* Update ind_gen from idt.v to accomodate the changes made to the parameters of *)
(* the new datatype. *)
(* ind_gen' glues the datatype information together so then Metacoq synthesizes it *)

#[universes(polymorphic)]
Definition ind_gen' (name : ident) (ctors : list (ident * term))
           (mind : mutual_inductive_body) (i : nat) : TemplateMonad unit :=
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
      let univ := Monomorphic_ctx (LevelSetProp.of_list [], ConstraintSet.empty) in
      let ind' :=
        {| ind_finite := mind.(ind_finite);
           ind_npars := mind.(ind_npars) + 1;
           ind_universes := univ;
           ind_variance := mind.(ind_variance);
           ind_params := indparam;
           ind_bodies := [ {| ind_name := name;
                              ind_type  := ty;
                              ind_kelim := ind.(ind_kelim);
                              ind_ctors := ctors;
                              ind_projs := ind.(ind_projs);
                              ind_relevance := ind.(ind_relevance) |} ]
        |}
      in
      (* t <- tmEval all ind' ;; *)
      (* tmPrint t ;; *)
      tmMkInductive' ind'
      (* tmReturn tt *)
  | _ => tmFail "No body found"
  end.


(* Synthesize the functorial representation of T *)
MetaCoq Run (
          (* Quote T into metacoq *)
          '(mind, i) <- tsf_get_mind ltac:(quote_term T (fun t => exact t));;
                                           (* tmReturn tt  *)
          (* Quotes the new types of the constructors into metacoq *)
          let ctorsT := ltac:(tsf_ctors_to_tm newT_ctors) in
          (* Synthesize the functorial representation of T as Fname *)
          ind_gen' Fname ctorsT mind i
        ).

(* ------- EDIT here ------ *)

(* The term generated as Fname *)
Notation TF := treeF.

(* ------------------------ *)

Definition FmapT(A B : Set)(F : Set -> Set) : Set := forall(f : A -> B), F A -> F B.

Definition FmapId(F : Set -> Set)(fmap : forall{A B : Set}, FmapT A B F) : Set :=
  forall (A : Set) (x : F A), fmap (fun x => x) x = x .

Class Functor (F : Set -> Set) :=
  {
  fmap : forall {A B : Set}, FmapT A B F;
  fmapId : FmapId F (@fmap)
  }.

Ltac intro_params S :=
  let rec go U := match U with
                      | forall (A : Set), ?V => refine (forall (A: Set), (_ : Set)); go V
                      | _ => idtac
                  end in
  let SU := type of S in
  go SU.

Ltac buildTF :=
  let rec go S := lazymatch goal with
                      | [A : Set |- _ ] => refine (_ A); clear A; go S
                      | _ => exact S
                  end in
  go TF.

Definition TF_F : Set -> Set.
Proof.
  intros X.
  intro_params T.
  revert X; intros X.
  buildTF.
Defined.

Definition TFMap_ty : Type.
Proof.
  intro_params T.
  refine (forall X1 X2, FmapT X1 X2 (fun X => _)).
  clear X1 X2.
  buildTF.
Defined.

Ltac get_constr t :=
  match goal with
      | [ H : t = ?C |- _ ] => get_head C
  end.


Definition TFmap : TFMap_ty.
Proof.
  unfold TFMap_ty; intros.
  unfold FmapT.
  intros f t.

  destruct t eqn:Teq;
  let constr := get_constr t in pose constr as C;

  match goal with
      | [ H : t = ?C |- _ ] => pose C as ct
  end;

  let rec go c := match c with
                      | ?C ?a => match type of a with
                                   | X1 => refine (_ (f a)); go C
                                   | _ => match a with
                                             | X1 => refine (_ X2); go C
                                             | _ => refine (_ a); go C

                                         end
                               end
                      | _ => exact C
                  end
  in
  let c := (eval unfold ct in ct) in
  go c.
Defined.

(* Definition FmapId(F : Set -> Set)(fmap : forall{A B : Set}, FmapT A B F) : Set := *)
(*   forall (A : Set) (x : F A), fmap (fun x => x) x = x . *)

Definition TFFunctor_ty : Type.
  intro_params T.
  refine (Functor (fun X => _)).
  buildTF.
Defined.

Hint Unfold TFFunctor_ty.


Definition TFMapId_ty : Type.
  intro_params T.
  refine (FmapId ltac:(buildTF) _).
  eapply TFmap.
Defined.

Definition TFMapId : TFMapId_ty.
  unfold TFMapId_ty; intros.
  unfold FmapId; intros X t.

  destruct t; reflexivity.
Defined.

Instance TFunctor : (unfolded TFFunctor_ty) :=
  { fmap := ltac:(eapply TFmap; eauto);
      fmapId := ltac:(eapply TFMapId; eauto)
  }.


