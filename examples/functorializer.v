From idt Require Import all.
From MetaCoq.Template Require Import utils All.

(* This file converts a datatype to it's functorial representation
   using the interface described in dc-recursion/.../List.v *)

(* We start by defining some example datatypes that we to convert. We
   stick to Set for now in order to avoid dealing with universes.  *)

Inductive list' (A : Set) : Set :=
| nil'  : list' A
| cons' : A -> list' A -> list' A.

Arguments nil' {A}.
Arguments cons' {A} _ _.

Inductive tree (A B : Set) : Set :=
| mempty : tree A B
| mnode : A -> B -> tree A B -> tree A B -> tree A B.

(* ------------------------ *)

(* The first step in building a functor-based representation of a type is
   to build a new type that includes the functor's inductive parameter. *)

Ltac buildFunKind T :=
  let rec buildFunKind' K :=
  match K with
    (* Work our way down the kind of the source type: *)
        | forall (A :?Z), ?M =>  refine (forall (A : Z), _); buildFunKind' M
        (* Insert X as the last parameter of the new Functor: *)
        | ?U => exact (forall (X : Set), U)
    end in
  let K := type of T in
  buildFunKind' K.

(* Here are the kinds for the functorialization of lists, trees, and
   strings (these strings are from the standard library): *)

Example listF_Kind : Type := ltac:(buildFunKind list').
Print listF_Kind.

Example treeF_Kind : Type := ltac:(buildFunKind tree).
Print treeF_Kind.

Example stringF_Kind : Type := ltac:(buildFunKind string).
Print stringF_Kind.

(* This helper function gets the codomain of a type. *)
Ltac codTy ty :=
  match ty with
  | forall (_ : _), ?U => codTy U
  | ?U => U
  end.

(* This tactic constructs a deep embedding of the constructors for the
   functorial representation of the the type T, using X as the name for the parameter of the functor. *)
Ltac buildFunCtors X T :=
  tsf_ctors T (fun s => append s "F")
            (fun c R => pose (ctor := c);
               (* Now we refine each one of R parameters with `refine (forall A, _)` *)
                        (* And apply each one to R, to build its complete return type for each constructor *)
                        let rec rector ty := lazymatch ty with
                                             | forall (A : Set), ?U => refine (forall (A : Set), _);
                                                                       try specialize (ctor A);
                                                                       pose proof (R A) as R;
                                                                       rector U
                                             | _ => idtac
                                             end in
                        let Ty := type of R in
                        rector Ty;
                        let ctorTy := type of ctor in
                        (* We remember the type of the constructor as Cty *)
                        let Cty := codTy ctorTy in
                        (* Finally, to functorialize each constructor do the following: *)
                        let rec genFunCtor ty := lazymatch ty with
                                          (* If Cty appears as a type, change it to X *)
                                          | forall (A : Cty), ?U => refine (forall (A : X), _); genFunCtor U
                                          (* Everything else remains unchanged *)
                                          | forall A : ?S, ?U => refine (forall (A : S), _); genFunCtor U
                                          (* If Cty appears as the return type, change it to R *)
                                          | Cty => exact R
                                                         (* TODO: Add other cases for more complex datatypes *)
                                                 end in
                        genFunCtor ctorTy).

(* Generating some example constructor descriptions for the
   functorialization of lists, trees, and strings: *)
Example listF_emb : tsf_ctors_ty ltac:(buildFunKind list') :=
  ltac:(let X := fresh in buildFunCtors X list').

Example treeF_emb : tsf_ctors_ty ltac:(buildFunKind tree) :=
  ltac:(let X := fresh in buildFunCtors X tree).

Example stringF_emb : tsf_ctors_ty ltac:(buildFunKind string) :=
  ltac:(let X := fresh in buildFunCtors X string).

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

(* ind_gen' adapts [ind_gen] from idt.v to accomodate the changes made
   to the parameters of the new datatype. ind_gen' takes various bits
   of information about the source type and target functorial
   representation, and produces a deeply-embedded program in the
   TemplateMonad. Running MetaCoq over this program adds the new
   datatype definition to the environment. *)

Definition ind_gen' (T : Type) (name : ident) (ctors : list (ident * term))
           (mind : mutual_inductive_body) (i : nat) : TemplateMonad unit :=
  ty <- tmQuote T ;;
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
      tmMkInductive' ind'
  | _ => tmFail "No body found"
  end.

(* Generate the functorinal representation of lists: *)
MetaCoq Run (let T := list' in
             let TName := "listF" in
             let newFunSig : Type := ltac:(buildFunKind T) in
             let newFunCtors : tsf_ctors_ty (unfolded newFunSig) :=
               ltac:(let X := fresh in buildFunCtors X (unfolded T)) in
             '(mind, i) <- tsf_get_mind ltac:(quote_term (unfolded T) (fun t => exact t));;
             (* Quotes the new types of the constructors into metacoq *)
             let ctorsT := ltac:(tsf_ctors_to_tm (unfolded newFunCtors)) in
             (* Synthesize the functorial representation of T as Fname *)
             ind_gen' (unfolded newFunSig) TName ctorsT mind i
            ).
Print listF.

(* We can also generate the functorinal representation of other types by
   changing the values bound to T and TName in the previous expression: *)
MetaCoq Run (
          let T := string in
          let TName := "stringF" in
          let newFunSig : Type := ltac:(buildFunKind T) in
          let newFunCtors : tsf_ctors_ty (unfolded newFunSig) :=
            ltac:(let X := fresh in buildFunCtors X (unfolded T)) in
          '(mind, i) <- tsf_get_mind ltac:(quote_term (unfolded T) (fun t => exact t));;
          let ctorsT := ltac:(tsf_ctors_to_tm (unfolded newFunCtors)) in
          ind_gen' (unfolded newFunSig) TName ctorsT mind i
        ).
Print stringF.

MetaCoq Run (
          let T := tree in
          let TName := "treeF" in
          let newFunSig : Type := ltac:(buildFunKind T) in
          let newFunCtors : tsf_ctors_ty (unfolded newFunSig) :=
            ltac:(let X := fresh in buildFunCtors X (unfolded T)) in
          '(mind, i) <- tsf_get_mind ltac:(quote_term (unfolded T) (fun t => exact t));;
          let ctorsT := ltac:(tsf_ctors_to_tm (unfolded newFunCtors)) in
          ind_gen' (unfolded newFunSig) TName ctorsT mind i
        ).
Print treeF.
