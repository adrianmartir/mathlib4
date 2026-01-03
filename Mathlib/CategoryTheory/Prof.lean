/-
Copyright (c) 2026 Adrian Marti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Marti
-/

module

public import Mathlib.CategoryTheory.Category.Cat

@[expose] public section

namespace CategoryTheory

universe u v

/-- The type of profunctors from `X` to `Y`. -/
def Prof (X Y : Cat) := Xᵒᵖ × Y ⥤ Type u

def Prof.app {X Y} (p : Prof X Y) (x : X) (y : Y) := p.obj ⟨Opposite.op x, y⟩

def Prof.mapL {X Y} (p : Prof X Y) {x x' y} (f : x ⟶ x') (h : p.app x' y) : p.app x y :=
  p.map ⟨f.op, 𝟙 y⟩ h

def Prof.mapR {X Y} (p : Prof X Y) {x y y'} (h : p.app x y) (f : y ⟶ y') : p.app x y' :=
  p.map ⟨𝟙 (Opposite.op x), f⟩ h

def Prof.mpRight {X Y} (h : Prof X Y) {a b c} (f : h.app a b) (p : b = c) : h.app a c :=
  h.mapR f (eqToHom p)

def Prof.mpLeft {X Y} (h : Prof X Y) {a b c} (p : a = b) (f : h.app b c) : h.app a c :=
  h.mapL (eqToHom p) f

/-- `Category` instance for `Prof X Y`, inherited from the category structure on functors. -/
instance instCategoryProf (X Y : Cat) : Category (Prof X Y) where
  Hom H K := NatTrans H K
  id := NatTrans.id
  comp := NatTrans.vcomp

-- The action of functors on profunctors

def Prof.actLeft {X Y Z : Cat} (f : Z ⟶ X) (p : Prof X Y) : Prof Z Y :=
  Functor.comp (Functor.prod (Functor.op f.toFunctor) (Functor.id Y)) p

def Prof.actRight {X Y Z : Cat} (p : Prof X Y) (f : Z ⟶ Y) : Prof X Z :=
  Functor.comp (Functor.prod (Functor.id Xᵒᵖ) (f.toFunctor)) p

lemma Prof.actLeft_app {X Y Z : Cat} (f : Z ⟶ X) (p : Prof X Y) (x y) :
    (p.actLeft f).app x y = p.app (f.toFunctor.obj x) y := rfl

lemma Prof.actRight_app {X Y Z : Cat} (p : Prof X Y) (f : Z ⟶ Y) (x y) :
    (p.actRight f).app x y = p.app x (f.toFunctor.obj y) := rfl

/-- Apply a natural transformation between profunctors to a pair of objects. -/
def Prof.homApp {X Y} {h : Prof X Y} {k : Prof X Y} (f : h ⟶ k) (c : X) (d : Y) :
    h.app c d → k.app c d := fun x ↦ f.app _ x

def Prof.homAppL {X X' Y} {f : X ⟶ X'} {h : Prof X Y} {k : Prof X' Y} (s : h ⟶ k.actLeft f)
    (c : X) (d : Y) : h.app c d → k.app (f.toFunctor.obj c) d :=
  fun x ↦ s.app _ x

def Prof.homAppR {X Y Y'} {h : Prof X Y} {k : Prof X Y'} {f : Y ⟶ Y'} (s : h ⟶ k.actRight f)
    (c : X) (d : Y) : h.app c d → k.app c (f.toFunctor.obj d) :=
  fun x ↦ s.app _ x

end CategoryTheory
