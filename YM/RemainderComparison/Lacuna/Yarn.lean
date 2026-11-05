import YM.RemainderComparison.Lacuna.Rotisserie
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lacuna
open Function Filter Finset Lattice RG Wilson MeasureTheory ProbabilityTheory Ovens
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat Song Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes YM.Extra.Iteration
open Mosaic Mosaic.Verse WickReps Flues Lobby
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c:Side}{ι I J K κ μ : Type}{α:Type*}
open Vesuvius Marker Serif
variable (A:Manor G c ι α I)(B:Manor G c ι α J)(R:Manor G c ι α K)(a b:α) (P:BudgetPoint)(root:ι→Support c) (u:Set ι) (W:Vesuvius G c ι κ α) (k:ℕ) (v:α→ℝ)
-- witness of equality for whole signed.Al.Get shape from booked choices.
structure Vision : Prop where
    fountain (a:α)(X:Config G c)(β:Type) [Fintype β] [DecidableEq β] (Q: Census β) (z:ι→Poly Q) (p:β→ℝ) : Serif.Chorus Q p u z k →
       A.basin P Set.univ u z a X = B.basin P Set.univ u z a X + Lacuna.tint Q (v a)+ R.basin P Set.univ u z a X+ ∑' i,Vesuvius.books a u z W X i

-- orientation proof before evaluation all.TEST.(mark law scalar)
structure Landscape : Prop where
   rotates θ (x:Config G c) b : aurora u A P b (Seat.view θ x)=aurora u A P a x
variable (V: Vision A B R P u W k v)
structure Seeds (σB B₁ σ B₂ B₃ D₁ D₂:ℝ):Prop where
    raw : A.Templary Set.univ root P σB B₁
    model : B.Templary Set.univ root P σB B₂
    core : R.Templary Set.univ root P σB B₃
    leaked : W.Works P root u σ D₁ D₂
    exponent : 0≤σ
    wing : 0≤σB

local notation "C" => Lacuna.tint EmptyC
variable {σB B₁ σ B₂ B₃ D₁ D₂ hB hF p w q C₀ σ' :ℝ}
variable (S:Seeds A B R P root u W σB B₁ σ B₂ B₃ D₁ D₂)
include V S
lemma at_zero (b:α)(U:Config G c): aurora u A P b U=aurora u B P b U+v b+aurora u R P b U+ wray W u b U:=by
   apply Lacuna.color EmptyC
   let z:= fun (_:ι)=> (0:Poly EmptyC); have ht:= Lacuna.pureSong u k
   have he:=V.fountain b U _ EmptyC z _ ht
   simp_rw [Lacuna.sunset A P z b U S.raw S.wing ht,Lacuna.sunset B P z b U S.model S.wing ht,Lacuna.sunset R P z b U S.core S.wing ht, Lacuna.farm P W z b U S.leaked S.exponent ht] at he
   unfold z at he; simp_rw [Lacuna.blankDay (u:=u), Lacuna.blankMark, add_zero] at he; simp_rw [tone_add]; exact he
variable (h: Landscape A a P u)(hl:Landscape B a P u)
include h hl
lemma meadow (U:Config G c) (b:α): v b+aurora u R P b U+wray W u b U= v a+ revolves (fun t:Seat c=> aurora u R P a (t.view U))+ revolves (fun t: Seat c=>wray W u a (t.view U)):=by
   let x t:= aurora u R P a ((t:Seat c).view U); let y t:=wray W u a ((t:Seat c).view U)
   let p (t:Seat c):=v a; have he: revolves p=v a:= Lacuna.still _ (fun _=>rfl)
   have ht (t:Seat c) : v b+aurora u R P b U+wray W u b U= ((p+x)+y) t:=by
      have hv:= at_zero A B R P root u W k v V S b U; have hv':= at_zero A B R P root u W k v V S a (t.view U)
      rw [h.rotates t U a,hl.rotates t U a] at hv'
      have hk := h.rotates (Jolt.standing c) U b; have hf:=hl.rotates (Jolt.standing c) U b; rw [Jolt.stamp] at hk hf
      rw [hk,hf] at hv; simp_rw [add_assoc] at hv' hv; rw [hv] at hv'; change _=v a+aurora u R P a _+wray W u a _; rw [add_assoc,add_assoc]; exact add_left_cancel hv'
   exact (Lacuna.still _ (fun t=> (ht t).symm)).symm.trans (by rw [Lacuna.refrains, Lacuna.refrains, he])

variable [Countable κ]
-- *unmerged* mask.Later attach other render receipts.Prepared during canon
structure Treated (R:Manor G c ι α K)(W:Vesuvius G c ι κ α)(σ dB d₁ σ' e₁ e₂:ℝ): Prop where
    view : Lacuna.Angular R u P σ dB
    fares : R.Spinal (Lobby.night R u)ᶜ root P σ d₁
    kernel : Jolt.Whirls (Lacuna.rudder W u a) u ∧ Scone.Rises (Lacuna.rudder W u a) P root∧ Scone.Treasures (Lacuna.rudder W u a) u k P.B σ' e₁ e₂
-- equality after.FX pre. Derivative marks not shifted.

omit h hl V in
lemma invested (hσ : 0≤σ') (hx:R.Templary (night R u) root P σ' q) (hp: R.Spinal (Lobby.night R u)ᶜ root P σ' C₀) : Treated a P root u k R W σ' q C₀ σ D₁ D₂:=by exact ⟨Lacuna.angular R P u hx hσ,hp,Lacuna.turns W u a,Lacuna.feeds W P u a root S.leaked⟩ -- linter include
open GridRenewal.Rain
variable {β:Type} [Fintype β][DecidableEq β]
local notation "L₀"=> rudder W u a
lemma pouring (Q:Census β) (z:ι→Poly Q)(p:β→ℝ)(hp: Serif.Chorus Q p u z k)(U:Config G c): HasSum (Vesuvius.books b u z W U) (∑' i,Vesuvius.books b u z W U i) ∧ Summable ((L₀).plume u z b U) ∧
       A.basin P Set.univ u z b U=B.basin P Set.univ u z b U+ Lacuna.tint Q (v a+Lacuna.scalar R P u a+ Vowel.overlay (Lacuna.exterior R u a) P U)+ Lacuna.day Q u R P z b U+
          (∑' i, (Lacuna.rudder W u a).plume u z b U i):=by
    have he:=V.fountain b U _ Q z p hp; rw [Lacuna.sunset R P z b U S.core S.wing hp,Lacuna.farm P W z b U S.leaked S.exponent hp] at he
    have hx:= Lacuna.meadow A B R a P root u W k v V S h hl U b
    have hh:= Lacuna.flumes W P u a b root U z S.leaked S.exponent hp
    rw [← Lacuna.ray_keeps R P u (S.core.skim (Set.subset_univ _) le_rfl le_rfl) S.wing a U] at hx
    refine ⟨(Vesuvius.pi_support P root k b u z W S.leaked S.exponent hp U).hasSum,hh.summable,?_⟩
    rw [he,hh.tsum_eq]; have hv:= congr_arg (Lacuna.tint Q) hx; simp_rw [tone_add] at hv ⊢
    linear_combination hv
end YM.RemainderComparison.Lacuna
