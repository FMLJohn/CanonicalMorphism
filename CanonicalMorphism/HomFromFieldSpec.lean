/-
Copyright (c) 2025 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Morphism from the spectrum of a field to a locally ringed space
In this file, we construct the following:
Given a locally ringed space `X`, a point `x : X`, a commutative ring `F` with
`hF : IsField F` and a local ring homomorphism `f : X.presheaf.stalk x ⟶ F`,
`AlgebraicGeometry.LocallyRingedSpace.HomFromFieldSpec x F hF f` is the
morphism from the spectrum of `F` to `X` induced by `f`.
Details of our construction:
1. For the continuous function from the topological space of `Spec F` to the topological space of
   `X`, we define it as the constant map `fun _ => x`.
2. `(HomFromFieldSpec x F hF f).c` belongs to the type
                `X.presheaf ⟶ ⟨fun _ => x, continuous_const⟩ _* (Spec F).presheaf`.
   In other words, in order to construct `(HomFromFieldSpec x F hF f).c`, we need to define a map
   from
                                        `X.presheaf.obj O`
   to
                  `(⟨fun _ => x, continuous_const⟩ _* (Spec F).presheaf).obj O`
   for any
                                        `O : (Opens X)ᵒᵖ`.
   We construct it by considering the cases `x ∈ O.unop` and `x ∉ O.unop` separately. It is not
   very difficult to prove the naturality of the map we have defined.
3. The most complicated part is completing `(HomFromFieldSpec x F hF f).prop`, in which we need to
   show that for any `x1 : Spec F`, the stalk map induced by our construction is a local ring
   homomorphism. We achieve this by observing that the the stalk map can actually be written as
   `RingHom.comp g h` for some `g` and `h`. We then show that both `g` and `h` are local, and use
   the fact that a composition of two local ring homomorphisms is local. In order to show that `g`
   is local, we prove that both the domain and the codomain of `g` are fields; it is true that if
   the domain and codomain of some ring homomorphism are both fields, then the homomorphism is local
   (see `isLocalHom_of_isField_of_isField`). To prove `h` is local, we show that `h` is essentially
   a composition of `f` and some isomorphism (see `stalkFunctor_map_natTrans_eq`).
-/

/-- If the domain and codomain of a ring homomorphism are both fields, then the homomorphism is
local. -/
theorem RingHom.isLocalHom_of_isField_of_isField
    {R : CommRingCat} {S : CommRingCat} (hR : IsField R) (hS : IsField S) (f : R →+* S) :
    IsLocalHom f := IsLocalHom.mk fun r hfr => by
  rw [isUnit_iff_exists] at hfr ⊢
  have hfr0 : f r ≠ 0 := fun h => by
    have := hS.nontrivial
    rw [h] at hfr
    simp only [zero_mul, zero_ne_one, mul_zero, and_self, exists_const] at hfr
  have hr0 : r ≠ 0 := fun h => by rw [h, map_zero] at hfr0; exact hfr0 rfl
  obtain ⟨s, hs⟩ := hR.mul_inv_cancel hr0
  exact ⟨s, hs, by rw [mul_comm]; exact hs⟩

namespace AlgebraicGeometry

instance SheafedSpace.CommRingCat.section_over_bot_unique
    {X : SheafedSpace CommRingCat} : Unique (X.presheaf.obj (Opposite.op ⊥)) where
  default := 0
  uniq := fun a => by
    let U : Empty → TopologicalSpace.Opens X.toPresheafedSpace := fun _ => ⊥
    let h := TopCat.Sheaf.eq_of_locally_eq X.sheaf U
    simp only [IsEmpty.forall_iff, true_implies] at h
    rw [congrArg X.sheaf.val.obj (congrArg Opposite.op <| show _ = ⊥ by
      simp only [iSup_eq_bot, IsEmpty.forall_iff])] at h
    exact h a 0

noncomputable instance Spec.structureSheaf.section_over_bot_unique
    {R : Type _} [CommRing R] : Unique ((Spec.structureSheaf R).val.obj (Opposite.op ⊥)) := by
  rw [show (Spec.structureSheaf R).val.obj { unop := ⊥ } =
    (Spec (CommRingCat.of R)).presheaf.obj { unop := ⊥ } by rfl]
  exact SheafedSpace.CommRingCat.section_over_bot_unique

end AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace TopCat

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X : LocallyRingedSpace} (x : X)
variable (F : CommRingCat) (hF : IsField F)
variable (f : X.presheaf.stalk x →+* F) [IsLocalHom f]

namespace HomFromFieldSpec

/-- The map of sections on `O` induced by `(HomFromFieldSpec x F hF f).c` for the case
`x ∈ O.unop`. -/
noncomputable def valCAppOpensOfMem (O : (Opens X)ᵒᵖ) (hxO : x ∈ O.unop) :
    X.presheaf.obj O ⟶
    (⟨fun _ => x, continuous_const⟩ _* (Spec F).presheaf).obj O :=
  let hom1 := Presheaf.germ X.presheaf O.unop x hxO
  let hom2 := CategoryStruct.comp (CommRingCat.ofHom f) (StructureSheaf.toOpen F ⊤)
  CategoryStruct.comp hom1 (CategoryStruct.comp hom2 ((Spec F).presheaf.map (Opens.leTop _).op))

/-- The map of sections on `O` induced by `(HomFromFieldSpec x F hF f).c` for the case
`x ∉ O.unop`. -/
noncomputable def valCAppOpensOfNotMem (O : (Opens X)ᵒᵖ) (hxO : x ∉ O.unop) :
    X.presheaf.obj O ⟶
    (⟨fun _ => x, continuous_const⟩ _* (Spec F).presheaf).obj O :=
  CommRingCat.ofHom {
    toFun := fun _ => 0
    map_one' := by
      have : ((Opens.map (@ContinuousMap.mk _ _ (PresheafedSpace.carrier
          (Spec F).toPresheafedSpace).str _ (fun _ => x) continuous_const))).op.obj O = op ⊥ := by
        simp only [Functor.op_obj, op.injEq]
        exact le_bot_iff.mp fun _ => hxO
      rw [this]
      exact subsingleton_iff_zero_eq_one.mpr <| @Unique.instSubsingleton _
        Spec.structureSheaf.section_over_bot_unique
    map_mul' := by simp_rw [mul_zero, implies_true]
    map_zero' := rfl
    map_add' := by simp_rw [add_zero, implies_true] }

/-- The map of sections on `O` induced by `(HomFromFieldSpec x F hF f).c`. -/
noncomputable def valCAppOpens (O : (Opens X)ᵒᵖ) :
    X.presheaf.obj O ⟶
    (⟨fun _ => x, continuous_const⟩ _* (Spec F).presheaf).obj O :=
  letI := Classical.propDecidable (x ∈ O.unop)
  if hxO : x ∈ O.unop then valCAppOpensOfMem x F f O hxO
  else valCAppOpensOfNotMem x F O hxO

omit [IsLocalHom f] in
/-- `valCAppOpens` satisfies the natural property, which is an important basis for our construction
of the morphism from `Spec F` to `X`. -/
theorem valCAppOpens_naturality {O1 O2 : (Opens X)ᵒᵖ} (i : O1 ⟶ O2) :
    CategoryStruct.comp (X.presheaf.map i) (valCAppOpens x F f O2) =
    CategoryStruct.comp (valCAppOpens x F f O1)
    ((⟨fun _ => x, continuous_const⟩ _* (Spec F).presheaf).map i) := by
  ext s
  rw [valCAppOpens, valCAppOpens]
  by_cases hxO2 : x ∈ O2.unop
  · have hxO1 : x ∈ O1.unop := le_of_op_hom i hxO2
    simp only [hxO2, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hxO1]
    erw [RingHom.comp_apply, Presheaf.germ_res_apply X.presheaf]
    rfl
  · simp only [hxO2]
    have : Unique (((Spec F).presheaf.obj
        { unop := (Opens.map ⟨fun _ => x, continuous_const⟩).obj O2.unop })) := by
      rw [(le_bot_iff.mp fun _ => hxO2 : (@Opens.map (Spec F) X.toTopCat
        ⟨fun _ => x, continuous_const⟩).obj _ = ⊥)]
      exact Spec.structureSheaf.section_over_bot_unique
    exact Eq.trans (this.eq_default _) (this.default_eq _)

/-- `(FirstCocone x F).ι.app = fun O => (IsoForFirstCocone x F O).hom`. -/
noncomputable def IsoForFirstCocone (O : (OpenNhds x)ᵒᵖ) :
    (Spec.structureSheaf F).val.obj (op ((Opens.map ⟨fun _ => x, continuous_const⟩).obj
    ((OpenNhds.inclusion x).obj O.unop))) ≅ F :=
  Iso.trans
    (eqToIso <| by
      rw [Opens.map]; simp only; congr; simp only [Set.preimage_eq_univ_iff]; intro x' h;
      change ∃ _, x = x' at h; rcases h with ⟨_, h1⟩; rw [← h1]; exact O.1.2)
    (StructureSheaf.globalSectionsIso F).symm

/-- As mentioned in the description of this file, there is a map `g` for which we want to show that
both the domain and codomain are fields. The domain of `g` is actually a colimit in terms of some
functor. Here we construct a concone in terms of the same functor. Note that `(FirstCocone x F).pt`
is defined as `F`. If we can prove that this cocone is a colimit, then because
colimits are unique up to isomorphisms, we will immediately have that the domain of `g` is
isomorphic to `F`. As `F` is a field, the domain of `g` is a field, which is what we want. -/
noncomputable def FirstCocone :
    Limits.Cocone ((OpenNhds.inclusion x).op.comp
    ((Opens.map ⟨fun _ => x, continuous_const⟩).op.comp (Spec.structureSheaf F).val)) where
  pt := F
  ι := {
    app := fun O => (IsoForFirstCocone x F O).hom
    naturality := fun O1 O2 i => by
      have hO (O : (OpenNhds x)ᵒᵖ) : (Opens.map (@ContinuousMap.mk _ _ (PrimeSpectrum.Top F).str _
          (fun _ => x) continuous_const)).obj ((OpenNhds.inclusion x).obj O.unop) = ⊤ := by
        ext
        simp only [Opens.coe_top, Set.mem_univ, iff_true]
        exact O.1.2
      have heqToHom1 : ((Opens.map ⟨fun _ => x, continuous_const⟩).map
          ((OpenNhds.inclusion x).map i.unop)).op = eqToHom (by rw [hO O1, hO O2]) := rfl
      have heqToHom2 : (Spec.structureSheaf F).val.map
          ((Opens.map ⟨fun _ => x, continuous_const⟩).map ((OpenNhds.inclusion x).map i.unop)).op =
          eqToHom (by rw [hO O1, hO O2]) := by
        rw [heqToHom1, eqToHom_map]
      simp only [Functor.const_obj_obj, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
        Functor.const_obj_map, IsoForFirstCocone, Iso.trans_hom, eqToIso.hom, Iso.symm_hom,
        StructureSheaf.globalSectionsIso_inv, IsIso.eq_comp_inv, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id, heqToHom2, eqToHom_trans] }

theorem FirstCocone.isColimit_fac (O : (OpenNhds x)ᵒᵖ)
    (s : Limits.Cocone ((OpenNhds.inclusion x).op.comp
      ((Opens.map ⟨fun _ => x, continuous_const⟩).op.comp (Spec.structureSheaf F).val))) :
    CategoryStruct.comp ((FirstCocone x F).ι.app O)
      ((fun s => CategoryStruct.comp (IsoForFirstCocone x F (op ⊤)).symm.hom
        (s.ι.app (op ⊤))) s) = s.ι.app O := by
  simp only [FirstCocone, IsoForFirstCocone, Iso.trans_hom, eqToIso.hom, Iso.symm_hom,
    StructureSheaf.globalSectionsIso_inv, eqToIso_refl, Iso.refl_trans, Iso.symm_symm_eq,
    StructureSheaf.globalSectionsIso_hom, Category.assoc, IsIso.inv_hom_id_assoc, eqToHom_comp_iff]
  rw [← eqToHom_map _ <| by rw [op_inj_iff]; ext; exact ⟨fun _ => O.1.2, fun _ => trivial⟩]
  exact Eq.symm (s.ι.naturality (op (LE.le.hom fun _ _ => trivial : O.unop ⟶ ⊤)))

/-- As mentioned in the description of this file, there is a map `g` for which we want to show that
both the domain and codomain are fields. The domain of `g` is actually a colimit in terms of some
functor. Recall that `FirstCocone x F` is a cocone in terms of the same functor and
`(FirstCocone x F).pt` is defined as `F`. This definition proves that `FirstCocone x F` is a
colimit. Because colimits are unique up to isomorphisms, this definition implies that the domain of
`g` is isomorphic to `F`. As `F` is a field, the domain of `g` is also a field, which is what we
want. -/
noncomputable def FirstCocone.isColimit : Limits.IsColimit (FirstCocone x F) where
  desc := fun s => CategoryStruct.comp (IsoForFirstCocone x F (op ⊤)).symm.hom (s.ι.app (op ⊤))
  fac := fun s O => FirstCocone.isColimit_fac x F O s
  uniq := fun s hom h => by simp only [Iso.symm_hom]; rw [(Iso.eq_inv_comp _).mpr (h _)]

/-- The domain of the map `g` mentioned in the description of this file is isomorphic to `F`. -/
noncomputable def FirstFieldIso :
    (⟨fun _ => x, continuous_const⟩ _* (Spec.structureSheaf F).val).stalk x ≅ F :=
  (Limits.colimit.isColimit ((OpenNhds.inclusion x).op.comp
  ((Opens.map ⟨fun _ => x, continuous_const⟩).op.comp
  (Spec.structureSheaf F).val))).coconePointUniqueUpToIso (FirstCocone.isColimit x F)

/-- `(SecondCocone F hF x1).ι.app = fun O => (IsoForSecondCocone F hF x1 O).hom`. -/
noncomputable def IsoForSecondCocone (x1 : Spec F) (O : (OpenNhds x1)ᵒᵖ) :
    (Spec.structureSheaf F).val.obj (op ((OpenNhds.inclusion x1).obj O.unop)) ≅ F :=
  Iso.trans
    (eqToIso <| by rw [show (OpenNhds.inclusion x1).obj O.unop = ⊤ by
      ext x2; rw [Eq.trans ((@PrimeSpectrum.instUnique _ hF.toField).eq_default x2)
      ((@PrimeSpectrum.instUnique _ hF.toField).default_eq x1)]; simp; exact O.1.2])
    (StructureSheaf.globalSectionsIso F).symm

/-- As mentioned in the description of this file, there is a map `g` for which we want to
show that both the domain and codomain are fields. The codomain of `g` is actually a colimit
in terms of some functor. Here we construct a concone in terms of the same functor. Note that
`(SecondCocone F hF x1).pt` is defined as `F`. If we can prove that this cocone is a colimit,
then because colimits are unique up to isomorphisms, we will immediately have that the codomain
of `g` is isomorphic to `F`. As `F` is a field, the codomain of `g` is a field, which is what we
want. -/
noncomputable def SecondCocone (x1 : Spec F) :
    Limits.Cocone ((OpenNhds.inclusion x1).op.comp (Spec.structureSheaf F).val) where
  pt := F
  ι := {
    app := fun O => (IsoForSecondCocone F hF x1 O).hom
    naturality := fun O1 O2 i => by
      have : ((OpenNhds.inclusion x1).map i.unop).op = eqToHom (by
          simp only [op.injEq]
          ext x2
          rw [Eq.trans ((@PrimeSpectrum.instUnique _ hF.toField).eq_default x2)
            ((@PrimeSpectrum.instUnique _ hF.toField).default_eq x1)]
          exact ⟨fun _ => O2.1.2, fun _ => O1.1.2⟩) := eq_of_comp_right_eq fun {_} => congrFun rfl
      simp only [Functor.const_obj_obj, Functor.comp_map, Functor.op_map, Functor.const_obj_map,
        Category.comp_id, IsoForSecondCocone, this, eqToHom_map, Iso.trans_hom, eqToIso.hom,
        eqToHom_trans_assoc] }

/-- As mentioned in the description of this file, there is a map `g` for which we want to show
that both the domain and codomain are fields. The codomain of `g` is actually a colimit in terms
of some functor. Recall that `SecondCocone F hF x1` is a cocone in terms of the same functor and
`(SecondCocone F hF x1).pt` is defined as `F`. This definition proves that `SecondCocone F hF x1`
is a colimit. Because colimits are unique up to isomorphisms, this definition implies that the
codomain of `g` is isomorphic to `F`. As `F` is a field, the codomain of `g` is also a field,
which is what we want. -/
noncomputable def SecondCocone.isColimit (x1 : Spec F) :
    Limits.IsColimit (SecondCocone F hF x1) where
  desc := fun s => CategoryStruct.comp (IsoForSecondCocone F hF x1 (op ⊤)).symm.hom
    (s.ι.app (op ⊤))
  fac := fun s O => by
    simp only [SecondCocone, IsoForSecondCocone, Functor.comp_obj, Functor.op_obj, Iso.trans_hom,
      eqToIso.hom, Iso.symm_hom, StructureSheaf.globalSectionsIso_inv, eqToIso_refl, Iso.refl_trans,
      Iso.symm_symm_eq, StructureSheaf.globalSectionsIso_hom, Category.assoc,
      IsIso.inv_hom_id_assoc, eqToHom_comp_iff]
    rw [← eqToHom_map _ (by
      simp only [op.injEq]
      ext x2
      simp only [Opens.coe_top, Set.mem_univ, true_iff]
      rw [Eq.trans ((@PrimeSpectrum.instUnique _ hF.toField).eq_default x2)
        ((@PrimeSpectrum.instUnique _ hF.toField).default_eq x1)]
      exact O.1.2)]
    exact Eq.symm (s.ι.naturality (op (LE.le.hom fun _ _ => trivial : O.unop ⟶ ⊤)))
  uniq := fun s hom h => by
    simp_rw [← h _, SecondCocone]
    rw [← Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.id_comp]

/-- The codomain of the map `g` mentioned in the description of this file is isomorphic to `F`. -/
noncomputable def SecondFieldIso (x1 : Spec F) :
    Presheaf.stalk (Spec.structureSheaf F).val x1 ≅ F :=
  letI := Limits.HasColimitsOfShape.has_colimit
    ((OpenNhds.inclusion x1).op.comp (Spec.structureSheaf ↑F).val)
  (Limits.colimit.isColimit ((OpenNhds.inclusion x1).op.comp
    (Spec.structureSheaf F).val)).coconePointUniqueUpToIso (SecondCocone.isColimit F hF x1)

omit [IsLocalHom f] in
/-- The map `h` mentioned in the description of this file is essentially a composition of `f` and
some ring isomorphism. -/
theorem stalkFunctor_map_natTrans_eq :
    (Presheaf.stalkFunctor CommRingCat x).map
    ⟨fun O => valCAppOpens x F f O, fun _ _ i => valCAppOpens_naturality x F f i⟩ =
    CategoryStruct.comp (CommRingCat.ofHom f) (FirstFieldIso x F).inv := by
  refine Eq.symm (Limits.IsColimit.uniq _ (Limits.Cocone.mk _ (CategoryStruct.comp (NatTrans.mk _ _)
    (Limits.colimit.cocone _).ι)) _ ?_)
  intro O
  have hxO (O : (OpenNhds x)ᵒᵖ) : x ∈ (OpenNhds.inclusion x).obj O.unop := O.1.2
  simp only [Functor.op_obj, NatTrans.comp_app, valCAppOpens, FirstFieldIso, hxO, reduceDIte,
    valCAppOpensOfMem, FirstCocone.isColimit, Limits.IsColimit.coconePointUniqueUpToIso,
    Functor.mapIso_inv, Limits.IsColimit.uniqueUpToIso_inv, Limits.Cocones.forget_map,
    Category.assoc, Limits.IsColimit.descCoconeMorphism_hom, CommRingCat.ofHom_comp]
  congr
  exact Eq.symm (Limits.colimit.w ((OpenNhds.inclusion x).op.comp
    ((Opens.map ⟨fun _ => x, continuous_const⟩).op.comp (Spec.structureSheaf F).val))
    (opHomOfLE fun _ _ => trivial : op ⊤ ⟶ O))

end HomFromFieldSpec

open HomFromFieldSpec

/-- The locally ringed space morphism from `Spec F` to `X` induced by `f`. -/
noncomputable def HomFromFieldSpec : (Spec F).toLocallyRingedSpace ⟶ X
    where
  base := ⟨fun _ => x, continuous_const⟩
  c := ⟨fun O => valCAppOpens x F f O, fun O1 O2 i => valCAppOpens_naturality x F f i⟩
  prop := fun x1 => by
    let g := Presheaf.stalkPushforward _ ⟨fun _ => x, continuous_const⟩
      (Spec.structureSheaf F).val x1
    let h := (Presheaf.stalkFunctor _ x).map
      ⟨fun O => valCAppOpens x F f O, fun O1 O2 i => valCAppOpens_naturality x F f i⟩
    haveI : IsLocalHom g.hom := RingHom.isLocalHom_of_isField_of_isField
      (MulEquiv.isField F hF (FirstFieldIso x F).commRingCatIsoToRingEquiv)
      (MulEquiv.isField F hF (SecondFieldIso F hF x1).commRingCatIsoToRingEquiv) g.hom
    haveI : IsLocalHom h.hom := by
      change IsLocalHom ((Presheaf.stalkFunctor CommRingCat x).map _).hom
      erw [stalkFunctor_map_natTrans_eq]
      exact CommRingCat.isLocalHom_comp (CommRingCat.ofHom f) (FirstFieldIso x F).inv
    exact RingHom.isLocalHom_comp g.hom h.hom

end AlgebraicGeometry.LocallyRingedSpace
