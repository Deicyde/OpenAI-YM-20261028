import YM.UVExtension.Projection.Read
import YM.Next.STATIONARY.Loops.Curvature

/-! Resolve simultaneous ambiguity across all periods of a fixed level. Hilbert topology after price & ratio. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Projection
open Lattice RG Exterior Precision Wilson Tree Bloch Laurent Stationary Filter Function Finset
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {p : Clip}
abbrev Crates (G : Gauge) := Chip G 1 ⊕ Chip G 2 ⊕ Chip G 3
abbrev Cube (G : Gauge):= Ortho (Crates G)
structure Rates (G : Gauge) where
    stageSide : ℕ → Side
    grainWidth : ℝ
    mold : ℝ -- from paths pre-L
    coil : ℝ -- from thermal cap at m
    width_pos : 0 < grainWidth
    mold_pos : 0 < mold
    coil_pos : 0 < coil

namespace Rates
variable (P : Rates G)
def evB := issue ∘ blend (G:=G) (I:=Crates G) Sum.inl P.grainWidth P.coil
def ev3 := issue ∘ blend (G:=G) (I:=Crates G) (n:=2) (Sum.inr ∘ Sum.inl) P.grainWidth P.mold
def ev4 := issue ∘ blend (G:=G) (I:=Crates G) (n:=3) (Sum.inr ∘ Sum.inr) P.grainWidth P.mold
def path (M : Bed) (x : Cube G) := emitBase G M (P.evB x) (P.ev3 x) (P.ev4 x)
structure Inked (x : Cube G) : Prop where
  two i: (P.evB x i).Invariant
  three i: (P.ev3 x i).Invariant
  four i: (P.ev4 x i).Invariant
  normal i j l : (∑' k, penny (P.evB x) i j k*lag (P.evB x) l k)=0

def hat (x : Cube G) (i : ℕ) := turnSeries (m:=P.stageSide i) (P.ev3 x)+turnSeries (P.ev4 x)
theorem hat_an (x : Cube G) (i : ℕ) : AnalyticAt ℝ (P.hat x i) 0 :=
    .add (turns_analytic _ (half_pos P.width_pos) (budget_hyp (Sum.inr∘Sum.inl) _ P.mold _ (half_lt_self P.width_pos)))
         (turns_analytic _ (half_pos P.width_pos) (budget_hyp (Sum.inr∘Sum.inr) _ P.mold _ (half_lt_self P.width_pos)))
lemma hat_cost (j : ℕ) (i v) : RLinear fun x => iteratedFDeriv ℝ j (P.hat x i) 0 v := by
  unfold hat
  exact RLinear.charge (fun x=> P.hat_an x i) (fun q=> (signed_linear (c:=P.mold) (Sum.inr∘Sum.inl) P.width_pos (input _ _ q)).add (signed_linear (c:=P.mold) (Sum.inr∘Sum.inr) P.width_pos (input _ _ q))) j _
def eHat (x : Cube G) (i : ℕ) := turnSeries (m:=P.stageSide i) (P.evB x)
theorem e_cost (j : ℕ) (i v) : RLinear fun x=> iteratedFDeriv ℝ j (P.eHat x i) 0 v:= in_turn Sum.inl P.width_pos _ _

def Blur (x : Cube G) : Prop := P.Inked x ∧ ∀ i,
  (∀ j,j ≤ 4 → ∀ v, iteratedFDeriv ℝ j (P.hat x i) 0 v=0) ∧ ∀ v,iteratedFDeriv ℝ 2 (P.eHat x i) 0 v=0
end Rates

section zero
variable {X I J : Type*} [AddCommGroup X] [Module ℝ X]
structure Preset (p : X → Prop) : Prop where
    zero : p 0
    add : ∀ x y, p x → p y → p (x+y)
    smul : ∀ a : ℝ, ∀ x, p x → p (a • x)
namespace Preset
theorem pair {p q : X→Prop} (h : Preset p) (he : Preset q) : Preset (fun x=> p x ∧ q x):=
    ⟨⟨h.zero,he.zero⟩, fun x y hp hh=> ⟨h.add x y hp.1 hh.1,he.add x y hp.2 hh.2⟩,fun _ _ hp=> ⟨h.smul _ _ hp.1, he.smul _ _ hp.2⟩⟩
theorem both {p : I→X→Prop} (h : ∀ i,Preset (p i)):Preset fun x=>∀ i,p i x:=
    ⟨fun i=> (h i).zero, fun x y hp he i=> (h i).add x y (hp i) (he i), fun _ _ hp i=> (h i).smul _ _ (hp i)⟩
theorem follow {p : X→Prop} {q : Prop} (h : q → Preset p):Preset fun x=> q → p x:=
    ⟨fun u=> (h u).zero, fun x y hp he i=> (h i).add x y (hp i) (he i), fun _ _ hp i=> (h i).smul _ _ (hp i)⟩
end Preset
end zero
section limit
variable {I E : Type}

def Strict (p : Ortho I→Prop) := Preset p ∧ ∀ {f : ℕ→ Ortho I} (x), HLimit f x → (∀ᶠ i in atTop,p (f i)) → p x
namespace Strict
theorem pair {p q : Ortho I→Prop} (h : Strict p) (he : Strict q) : Strict (fun x=> p x ∧ q x):=
    ⟨h.1.pair he.1,fun x hp hh=> ⟨h.2 x hp (hh.mono fun _ h=> h.1),he.2 x hp (hh.mono fun _ h=> h.2)⟩⟩
theorem both {p : E→ Ortho I→Prop} (h : ∀ i,Strict (p i)):Strict fun x=>∀ i,p i x:=
    ⟨Preset.both fun i=> (h i).1,fun x hp he i=> (h i).2 x hp (he.mono fun _ h=> h i)⟩
theorem follow {p : Ortho I→Prop} {q : Prop} (h : q→Strict p):Strict fun x => q→p x:=
    ⟨Preset.follow fun i=> (h i).1,fun x hp he i=> (h i).2 x hp (he.mono fun _ h=> h i)⟩
theorem linear {f g : Ortho I →ℝ} (h : RLinear f) (he : RLinear g) : Strict fun x=> f x=g x := by
  obtain ⟨p,rfl⟩:= h; obtain ⟨q,rfl⟩:= he
  exact ⟨⟨by simp,fun x y hp hh=> by simp [hp,hh],fun a x hp=> by simp [hp]⟩,fun _ hv hx=> tendsto_nhds_unique ((hv.bids (RLinear.mk p)).congr' hx) (hv.bids (RLinear.mk q))⟩
end Strict
end limit

namespace Rates
variable (P : Rates G)
lemma orient {n : ℕ} [NeZero n] (c : ℝ) (e : Chip G n → Crates G) : Strict fun (x:Cube G)=> ∀ i,(issue (blend e P.grainWidth c x) i).Invariant:=
    Strict.both fun i=> Strict.both fun _=> Strict.both fun _=> (Strict.linear (ink_poly _ i _) (ink_poly _ _ _))
lemma areas : Strict P.Inked := by
  let H x:= (∀ i,(P.evB x i).Invariant)∧(∀ i,(P.ev3 x i).Invariant)∧ (∀ i,(P.ev4 x i).Invariant) ∧ ∀ i j l,(∑' k,penny (P.evB x) i j k*lag (P.evB x) l k)=0
  have he : P.Inked=H:= funext fun x=> propext ⟨fun h=>⟨h.two,h.three,h.four,h.normal⟩,fun h=> ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩⟩
  rw [he]; exact (P.orient P.coil Sum.inl).pair (((P.orient P.mold (Sum.inr∘Sum.inl))).pair ((P.orient P.mold (Sum.inr∘Sum.inr)).pair (Strict.both fun i=> Strict.both fun j=> Strict.both fun l=> Strict.linear (penny_price _ P.width_pos i j l) (RLinear.mk 0))))
lemma stamps: Strict P.Blur:= P.areas.pair (Strict.both fun i=>
  (Strict.both fun j=> Strict.follow (fun _=> Strict.both fun v=> Strict.linear (P.hat_cost j i v) (RLinear.mk 0))).pair (Strict.both fun v=> Strict.linear (P.e_cost 2 i v) (RLinear.mk 0)))

def sub (p : Cube G →Prop) (h : Preset p) : Submodule ℝ (Cube G):= { carrier:={x|p x}, zero_mem':=h.zero,add_mem':= fun hp hh=> h.add _ _ hp hh, smul_mem':= fun _ _ hp=> h.smul _ _ hp }
def valid := sub P.Inked P.areas.1
def seam := sub P.Blur P.stamps.1

def Lodge (x : Cube G) := x∈P.seamᗮ ∧ x∈P.valid
lemma sealed (x : Cube G) (he : x∈P.valid):∃ z : Cube G, ‖z‖≤‖x‖ ∧ P.Lodge z ∧ x-z ∈ P.seam:=by
  have h : IsClosed (P.seam : Set (Cube G)):= (show IsSeqClosed _ from fun _ x hf hh=> P.stamps.2 x (HLimit.strong hh) (Eventually.of_forall hf)).isClosed
  obtain ⟨z,hz,h,H⟩:= Minimize P.seam x h
  change P.Blur _ at H
  exact ⟨z,hz,⟨h,(sub_sub_cancel _ _ : x-(x-z)=z) ▸ P.valid.sub_mem he (show x-z∈P.valid from H.1)⟩,H⟩
end Rates
end YM.UVExtension.Projection
