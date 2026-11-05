import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.DCompare
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.FrameCosts

/-!
# Uniform selected price gap: retain an actual window margin everywhere

Derivative shell comparator E02→F01 applied on the actual tree
and to flat data on that tree, *in a gauge localized to each active
bond*, not one global trivial gauge. Perturb comparison uses projected
row anchors with orientation included. Output flags actual; don't require
realizability of the proposed packets in a common U for this result.
Post-L constants and include color multiplicity. This isn't a claim of
any uniform curvature away from the active hull or a quantum spectral
bound.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Turn
open Matrix Work.F03 Progress.StationaryScenes Push.AbsoluteSums Tree Next.Fluctuations
open Win Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

section short

def straightF (S : StepData c f) (p : Cell f) : Pos S := (1,.inl (p,false))
def straightI (S : StepData c f) (i : Bond c) : Pos S := (1,.inr i)

def little (p : Pos S) : Prop := (∃ i,p=straightF S i) ∨ (∃ i,p=straightI S i)

lemma undiminished (T : Tube G S) (t R : ℕ) (p : Pos S) (hp : little p) (V : Config G c)
    (x : Directions G f) : derivative T t p V x = derivative T R p V x := by
  rcases hp with ⟨i,rfl⟩|⟨i,rfl⟩ <;> rfl

lemma section_flat (T : Tube G S) (R : ℕ) (x : Directions G f) (p : Cell f) :
    derivative T R (straightF S p) 1 x=Real.sqrt T.high.direct • curl p x := by
  unfold derivative; rw [untwine_flat _ rfl]; rfl

lemma rate_flat (T : Tube G S) (R : ℕ) (x : Directions G f) (i : Bond c) :
    derivative T R (straightI S i) 1 x= -(Real.sqrt S.kernel.penalty) • Bid.bills S (form x) (pole i) := by
  unfold derivative; rw [untwine_flat _ rfl]
  change Real.sqrt S.kernel.penalty • (0-Bid.bills S (form x) (pole i)) = _
  rw [neg_smul, zero_sub, smul_neg]

def city (D : Patch) := macroR D + D.L.val

def endowment (D : Patch) := city D + 4*stencilD D 0 + 1

lemma parcel (S : StepData c f) (e : Bond f) (y : Cover) (hy : y ∈ box (macroR S.patch)) :
    separation (home S e) (S.ratio.parent (wrap f y + S.ratio.embed (home S e))) ≤ city S.patch := by
  let i := S.ratio.embed (home S e)
  let p := wrap f y + i
  have hp := Corona.foreshorten S.ratio i p
  have hf : S.ratio.parent i=home S e := S.ratio.embed_parent _
  rw [hf] at hp
  have h1 := Work.E08.separation_box_add i hy
  exact (le_mul_of_one_le_left (Nat.zero_le (separation ..)) S.ratio.count.property).trans
    (hp.trans (Nat.add_le_add_right h1 _))

-- Any smaller price point, step order.

structure Warning (P : Teller G) (J : Patch) (t : ℝ) : Prop where
  adjust (c f : Side) (S : StepData c f) (T : Tube G S) : S.patch=J → P.Funds S T →
    ∀ (p : Pos S) (v : Directions G f) (C δ : ℝ), 0≤C → 0≤δ →
      let D := stencilD S.patch 0
      (∀ i : Bond f,separation (base S p) (home S i) ≤ D+1 → ‖v i‖ ≤ C) →
      ∀ V : Config G c,(∀ i : Bond c,separation (base S p) i.1 ≤ 4*D+1 → G.chord (V i) ≤ δ) →
      ‖derivative T 0 p V v-derivative T 0 p 1 v‖ ≤ t*δ*C

lemma warning (P : Teller G) (J : Patch) (h : J.Branches P.bind G) : ∃ t : ℝ, 0<t ∧ Warning P J t := by
  obtain ⟨Y,hY,he⟩ := perturb P J h
  refine ⟨Y*((4*stencilD J 0:ℕ)+1:ℝ),by positivity,⟨fun c f S T hJ hT p v C δ hC hd hv V hk => ?_⟩⟩
  have hy := he c f S T hJ hT 0 p v C δ hC hd hv V hk
  rw [hJ] at hy; exact hy

section tests

private lemma chart_gap (P : Teller G) (D : Patch) (x δ : ℝ) (T : Tube G S) (F : Forest S.ratio)
    (A : Stores S) (v : ArrayR G f) (V : Config G c) (e : Bond f) {t : ℝ} (hu : Warning P D t)
    (hD : S.patch=D) (hh : P.Funds S T) (hz : δ≥0) (z : Site c → G.El)
    (hb : ∀ i : Vars G f, i.1∉activeB A F (radiusB x) → v i=0)
    (hp : ∀ i : Bond c,separation (home S e) i.1 ≤ endowment D → G.chord (gauge z V i) ≤ δ)
    (hw : e∈activeB A F (radiusB x)) (hR : city D ≤ 2*radiusB x) :
    let u := lie v
    let u' := rotateG u (z ∘ S.ratio.parent)
    let g := purse (base S) (fun i => ‖descend (Dmat T F x A V *ᵥ v) i‖) (city D) (home S e)
    let L := purse (home S) (fun i => ‖u i‖) (endowment D) (home S e)
    let s := Real.sqrt weight
    ∀ (p : Pos S), separation (home S e) (base S p) ≤ city D → little p →
      ‖derivative T (till x) p 1 u'‖ ≤ s⁻¹*g + t*δ*L := by
  intro u u' G' L s p he hl
  let a := home S e; let r := stencilD D 0
  let W := gauge z V
  have hg : ∀ i : Bond f,separation (base S p) (home S i) ≤ stencilD S.patch 0+1 → ‖u' i‖ ≤ L := by
    intro i hi; unfold u' rotateG at *; rw [G.norm_adjoint]
    refine purse_le (home S) (fun i => ‖u i‖) (endowment D) (home S e) i (le_trans (separation_triangle _ (base S p) _) ?_)
    rw [hD] at hi; unfold endowment; omega
  have hV : ∀ i : Bond c,separation (base S p) i.1 ≤ 4*stencilD S.patch 0+1 → G.chord (W i) ≤ δ := by
    intro i hi; apply hp
    apply le_trans (separation_triangle _ (base S p) _)
    rw [hD] at hi; unfold endowment; omega
  have ht := hu.adjust _ _ S T hD hh p u' L δ (purse_ge ..) hz hg W hV
  let Y := derivative T 0 p W u'
  let b := derivative T 0 p V u
  have hs : 0 < s := Real.sqrt_pos.mpr weight_pos
  have hgl : ‖Y‖=‖b‖ := by
    have hy := derivative_gauge T 0 p V u z hh
    change Y = G.adjoint _ b at hy; rw [hy,G.norm_adjoint]
  rw [undiminished T _ 0 p hl]
  calc
    _ ≤ ‖Y‖ + ‖Y-derivative T 0 p 1 u'‖ := by
      rw [add_comm ‖Y‖,norm_sub_rev Y]; apply norm_le_norm_sub_add
    _ ≤ s⁻¹*G'+t*δ*L := by
      refine add_le_add ?_ ht; rw [hgl]
      apply le_of_mul_le_mul_left _ hs; rw [mul_inv_cancel_left₀ hs.ne']
      apply le_trans _ (purse_le (base S) (fun i => ‖descend (Dmat T F x A V *ᵥ v) i‖) _ _ p he)
      change _ ≤ ‖descend ..‖; rw [summit p V T A F x v hh (choose_span p A _ F hw (he.trans hR)) hb,
        undiminished T (till x) 0 p hl,norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg weight)]
end tests

-- Bill for a given local perturbation zone.
def debit (P : Teller G) (D : Patch) (C : ℝ) :=
    C * (box (macroR D)).card * (Fintype.card PlaqAxes) * (Real.sqrt P.top.clip.direct)⁻¹ + (Real.sqrt P.bind.penalty)⁻¹



lemma expense (P : Teller G) (D : Patch) (x : ℝ) (T : Tube G S) (F : Forest S.ratio)
    (A : Stores S) (v : ArrayR G f) (V : Config G c) (e : Bond f) {t : ℝ} (hu : Warning P D t)
    (hD : S.patch=D) (hh : P.Funds S T) {C : ℝ} (hC : 0≤C) (s : S.Choices)
    (hE : ∀ U : Config G f, SliceSet S F U → usable S U (home S e) s →
      Bid.Cops U (S:=S) 1 (S.prediction U s) e C) (hf : A.flags=RG.flags (temp x) V)
    (hb : ∀ i : Vars G f, i.1∉activeB A F (radiusB x) → v i=0)
    (hw : e∈activeB A F (radiusB x)) (hR : endowment D+1 ≤ radiusB x)
    (he : 2*(endowment D+1)<c.val) :
    let δ := tariff (endowment D+1) x
    let g := purse (base S) (fun i => ‖descend (Dmat T F x A V *ᵥ v) i‖) (city D) (home S e)
    let L := purse (home S) (fun i => ‖lie v i‖) (endowment D) (home S e)
    ‖lie v e‖ ≤ debit P D C * ((Real.sqrt weight)⁻¹*g + t*δ*L) := by
  intro δ g L
  have hE' : home S e∉A.dome (10*radiusB x) := fun hi => Finset.disjoint_left.mp
    (mem_filter.mp hw).2.2 (pin_origin ..) hi
  obtain ⟨z,hz⟩ := reduceV S V A x hf (endowment D+1) (endowment D) (by omega) (home S e)
    (fun hi => hE' (placed A (endowment D+1) _ (by omega) hi)) he
  have hd : 0≤δ := by unfold δ tariff; have hx := Work.E04.temp_nonneg x; positivity
  have hY : city D ≤ 2*radiusB x := by unfold endowment at hR; omega
  have hG := chart_gap P D x δ T F A v V e hu hD hh hd z hb hz hw hY
  let Z := rotateG (lie v) (z ∘ S.ratio.parent)
  have hZ i (hi : i∈F.trunks) : collect G (form Z) i=0 := by
    rw [collect_form]; have he : lie v i=(0:G.Color) := by
      ext j
      have hn : i ∉ activeB A F (radiusB x) := fun he => (mem_filter.mp he).2.1 hi
      exact hb (i,j) hn
    unfold Z rotateG; rw [he,map_zero]
  let hL := Work.F01.link_bound S (Push.SectorMeasure.funds_branch hh) F s (form Z) hZ C hC e hE
  let b := (Real.sqrt weight)⁻¹*g + t*δ*L; let a := home S e; let l := Real.sqrt P.top.clip.direct; let K := Real.sqrt S.kernel.penalty
  have hl : 0<l := Real.sqrt_pos.mpr P.top.clip.quadratic_pos
  have hk : 0<K := Real.sqrt_pos.mpr S.kernel.penalty_pos
  have hv (y : Cover) (hy : y∈box (macroR S.patch)) (p : PlaqAxes) :
      ‖curl (wrap f y + S.ratio.embed a,p) Z‖ ≤ l⁻¹*b := by
    let i : Cell f := (wrap f y + S.ratio.embed a,p)
    have ht : separation a (base S (straightF S i)) ≤ city D := by
      rw [show base S (straightF S i)=S.ratio.parent i.1 from rfl, ← hD]
      exact parcel S e y hy
    have hs := hG _ ht (Or.inl ⟨i,rfl⟩)
    apply le_of_mul_le_mul_left _ hl; rw [mul_inv_cancel_left₀ hl.ne']
    rw [section_flat T (till x) Z i, hh.high,norm_smul,Real.norm_of_nonneg hl.le] at hs; exact hs
  have ht : ‖Bid.bills S (form Z) (a,coord e.2)‖ ≤ K⁻¹*b := by
    let i : Bond c := (a,e.2)
    have hs := hG (straightI S i) (by simp [straightI,i,base,center,a]) (Or.inr ⟨i,rfl⟩)
    rw [rate_flat T (till x) Z i,norm_smul,norm_neg, Real.norm_of_nonneg hk.le] at hs
    apply le_of_mul_le_mul_left _ hk; rw [mul_inv_cancel_left₀ hk.ne']; exact hs
  rw [collect_form] at hL
  rw [← show ‖Z e‖=‖lie v e‖ from G.norm_adjoint ..]; apply hL.trans
  calc
    _ ≤ C*(∑ _y ∈ box (macroR S.patch),∑ _p : PlaqAxes,l⁻¹*b) + K⁻¹*b := add_le_add
        (mul_le_mul_of_nonneg_left (sum_le_sum fun y hy => sum_le_sum fun p _ => hv y hy p) hC) ht
    _ = _ := by simp only [sum_const,nsmul_eq_mul,card_univ,hD,debit]; unfold l b K; rw [hh.knobs]; ring
end short
end YM.AnalyticNext.ConnectedActivity.Aff
