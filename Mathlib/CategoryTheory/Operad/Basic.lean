/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Prof


/-!
A formalization of operads based on profunctors. We avoid using the bicategory of profunctors
and instead frame things in terms of `Unit` and `BiNatTrans`. This has the benefit
of avoiding the complexities of profunctor composition and gives
a computational interpretation of operads.

References:
* [A unified framework for generalized multicategories](https://arxiv.org/abs/0907.2460)
-/

@[expose] public section

namespace CategoryTheory

universe u v

abbrev Unit {X} (h : Prof X X) := (a : X) → h.app a a

/-- A natural transformation from a pair of profunctors to a third profunctor. -/
structure BiNatTrans {X Y Z} (h : Prof X Y) (k : Prof Y Z) (j : Prof X Z) where
  app {x y z} : h.app x y → k.app y z → j.app x z
  /-- The wedge property for `app`. -/
  wedge {x y y' z} (f : h.app x y) (α : y ⟶ y') (g : k.app y' z) :
    app (h.mapR f α) g = app f (k.mapL α g)
  /-- Naturality with respect to acting on the left. -/
  natL {x x' y z} (α : x' ⟶ x) (f : h.app x y) (g : k.app y z) :
    app (h.mapL α f) g = j.mapL α (app f g)
  /-- Naturality with respect to acting on the right. -/
  natR {x y z z'} (f : h.app x y) (g : k.app y z) (α : z ⟶ z') :
    app f (k.mapR g α) = j.mapR (app f g) α

def BiNatTrans.appL {X X' Y Z} {h : Prof X' Y} {k : Prof Y Z} {j : Prof X Z} {f : X' ⟶ X}
    (α : BiNatTrans h k (j.actLeft f)) (x y z) (s : h.app x y) (t : k.app y z) :
      j.app (f.toFunctor.obj x) z :=
  α.app s t

def BiNatTrans.appR {X Y Z Z'} (h : Prof X Y) {k : Prof Y Z} {j : Prof X Z'} {f : Z ⟶ Z'}
    (α : BiNatTrans h k (j.actRight f)) {x y z} (s : h.app x y) (t : k.app y z) :
      j.app x (f.toFunctor.obj z) :=
  α.app s t

/-- A functor from `Cat` to `Cat` is a *functor of profunctors* if it suitably maps profunctors
to profunctors in a way that is compatible with the action on functors.
Moreover, we wish to map units to units and binatural transformations to binatural transformations.
Most notably, this typeclass is missing preservation properties for vertical composition of
natural transformations, units and binatural transformations.

This a simplified variant of a *functor of equipments*. -/
class FunctorProf (T : Functor Cat Cat) where
  /-- Mapping action on profunctors and morphisms of profunctors. -/
  mapProf {X Y} : Prof X Y ⥤ Prof (T.obj X) (T.obj Y)
  /-- Functoriality with respect to the left action. -/
  mapProf_actLeft {X Y Z : Cat} (f : Z ⟶ X) (p : Prof X Y) :
    mapProf.obj (p.actLeft f) = (mapProf.obj p).actLeft (T.map f)
  /-- Functoriality with respect to the right action. -/
  mapProf_actRight {X Y Z : Cat} (p : Prof X Y) (f : Z ⟶ Y) :
    mapProf.obj (p.actRight f) = (mapProf.obj p).actRight (T.map f)
  /-- Mapping action on units. -/
  mapUnit {X} {h : Prof X X} : Unit h → Unit (mapProf.obj h)
  /-- Mapping action on binatural transformations. -/
  mapBi {X Y Z} {h : Prof X Y} {k : Prof Y Z} {j : Prof X Z} :
    BiNatTrans h k j → BiNatTrans (mapProf.obj h) (mapProf.obj k) (mapProf.obj j)

-- Mapping actions for cells

def FunctorProf.mapUnitL (T : Functor Cat Cat) [FunctorProf T] {X Y} {f : X ⟶ Y} {p : Prof Y X}
    (a : Unit (p.actLeft f)) : Unit ((mapProf.obj p).actLeft (T.map f)) :=
  mapProf_actLeft (T := T) f p ▸ (mapUnit (T := T) a)

def FunctorProf.mapUnitR (T : Functor Cat Cat) [FunctorProf T] {X Y} {p : Prof Y X} {f : Y ⟶ X}
    (a : Unit (p.actRight f)) : Unit ((mapProf.obj p).actRight (T.map f)) :=
  mapProf_actRight (T := T) p f ▸ (mapUnit (T := T) a)

def FunctorProf.mapBiL (T : Functor Cat Cat) [FunctorProf T] {X Y Z W} {f : X ⟶ Y}
    {p : Prof X Z} {q : Prof Z W} {r : Prof Y W}
    (a : BiNatTrans p q (r.actLeft f)) :
    BiNatTrans (mapProf.obj p) (mapProf.obj q) ((mapProf.obj r).actLeft (T.map f)) :=
  mapProf_actLeft (T := T) _ _ ▸ mapBi a

def FunctorProf.mapBiR (T : Functor Cat Cat) [FunctorProf T] {X Y Z W}
    (p : Prof X Y) (q : Prof Y Z) (r : Prof X W) (g : Z ⟶ W) (a : BiNatTrans p q (r.actRight g)) :
    BiNatTrans (mapProf.obj p) (mapProf.obj q) ((mapProf.obj r).actRight (T.map g)) :=
  mapProf_actRight (T := T) _ _ ▸ mapBi a


/-- A monad carrying a structure of a *functor of profunctors* is a *monad of profunctors*
if the corresponding naturality squares for profunctors can be filled by 2-cells.

We omit the corresponding monad laws for those cells. -/
class MonadProf (T : Monad Cat) extends FunctorProf T where
  η_prof {X Y} (h : Prof X Y) : h ⟶
    Prof.actLeft (T.η.app X) (Prof.actRight (mapProf.obj h) (T.η.app Y))
  μ_prof {X Y} (h : Prof X Y) : mapProf.obj (mapProf.obj h) ⟶
    Prof.actLeft (T.μ.app X) (Prof.actRight (mapProf.obj h) (T.μ.app Y))

lemma left_unit_obj {T : Monad Cat} {X} (a : T.obj X) :
    (T.μ.app _).toFunctor.obj ((T.η.app _).toFunctor.obj a) = a := by
  rw [<- CategoryTheory.Cat.Hom.comp_obj, Monad.left_unit]
  rfl

lemma right_unit_obj {T : Monad Cat} {X} (a : T.obj X) :
    (T.μ.app _).toFunctor.obj ((T.map (T.η.app _)).toFunctor.obj a) = a := by
  rw [<- CategoryTheory.Cat.Hom.comp_obj, Monad.right_unit]
  rfl

lemma assoc_obj {T : Monad Cat} {X} (a : T.obj (T.obj (T.obj X))) :
    (T.μ.app X).toFunctor.obj ((T.μ.app (T.obj X)).toFunctor.obj a)
      = (T.μ.app X).toFunctor.obj ((T.map (T.μ.app X)).toFunctor.obj a) := by
  rw [<- CategoryTheory.Cat.Hom.comp_obj, <- Monad.assoc]
  rfl

variable (T : Monad Cat) [MonadProf T]

abbrev Signature (X : Cat) := Prof (T.obj X) X

open Prof FunctorProf MonadProf

structure Operad (X : Cat) where
  hom : Prof (T.obj X) X
  id : Unit (actLeft (T.η.app X) hom)
  comp : BiNatTrans (mapProf.obj hom) hom (actLeft (T.μ.app X) hom)
  comp_id {a : X} {b : T.obj X} (f : hom.app b a) :
    comp.app (homAppL (η_prof hom) _ _ f) (id a) = hom.mpLeft (left_unit_obj b) f
  id_comp {a : X} (b : T.obj X) (f : hom.app b a) :
    comp.app ((mapUnitL T id) b) f = hom.mpLeft (right_unit_obj b) f
  comp_assoc  {a : X} {b : T.obj X} {c : T.obj (T.obj X)} {d : T.obj (T.obj (T.obj X))}
      (f : (mapProf.obj (mapProf.obj hom)).app d c) (g : (mapProf.obj hom).app c b)
      (h : hom.app b a) :
    assoc_obj _ ▸
      comp.appL ((T.μ.app _).toFunctor.obj d) ((T.μ.app _).toFunctor.obj c) a
        (homApp (μ_prof hom) d c f)
        (comp.app g h)
      = comp.appL ((T.map (T.μ.app _)).toFunctor.obj d) _ a ((mapBiL T comp).app f g) h


end CategoryTheory
