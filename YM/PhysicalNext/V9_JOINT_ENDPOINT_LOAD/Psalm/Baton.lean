import YM.AnalyticBridge.RESET_INCOME_PORT.BulkFare
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Currency
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Draught
import YM.Further.ROOTED_INTERACTING_REMAINDER.Protocol
import YM.Further.ROOTED_INTERACTING_REMAINDER.Vault
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Branches
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Sleeve
import YM.Planned.ATOM_REGULAR_ESTIMATE.Localization
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Insertion

/-! # Strict guard at the actual relative V/noise threshold, with tree
slice and all frame/connector rules still on tested U. Even on only-local
completion of the sector *at V* in its no-hole authorized region. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm
open Function Filter Set Lattice Wilson RG Tree Pressure Precision Next Next.SectorChange Wisps Bid
   Push.SectorMeasure WardBin.Lies Planned.AtomRegular.Foliage AnalyticBridge.LocalGaussianLaws
   AnalyticBridge.LocalGaussian Further.RootedInteractingRemainder Heir
open AnalyticNext.ConnectedActivity (Aff.tap_open Rates.allowance Rates.pieces Rates.slow)
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {k : S.Choices} {I : Type} [Fintype I]
    {X : Support f} {Y : Support c} {P B : BudgetPoint} {Pt : Teller G} {n : ℕ} {x u W r : ℝ} {q : Chi} {d : ℝ} {V : Config G c}
    {g : Site c → G.El} {C : Libretto G n} {D : Record}

structure Baton (G : Gauge) where
  cost : ℝ
  cash : ℝ
  large : 0 < cost
  small : 0 < cash
  pays (a : G.Color) : ‖a‖ ≤ cash → G.chord (G.lieExp a) ≤ cost*‖a‖
lemma baton_exists (G : Gauge) : Nonempty (Baton G) := by obtain ⟨a,b,ha,hb,h⟩ := Next.Fluctuations.chord_chart_cost G; exact ⟨a,b,ha,hb,h⟩

abbrev stride (H : Patch) := 2 + Push.GridApprox.reach H
abbrev coarseCost (C : Libretto G n) (H : Patch) := C.C*2*(1+(stride H:ℝ))
def tapCost (C : Libretto G n) (Bt : Baton G) (H : Patch) := Bt.cost* (storeCost C + coarseCost C H)
def battle (C : Libretto G n) (Bt : Baton G) (H : Patch) (K : KernelChoices) :=
    1+2*(Bt.cost*coarseCost C H + Vault.farePrice H K * (4*tapCost C Bt H))
structure Peace (C : Libretto G n) (Bt : Baton G) (H : Patch) (K : KernelChoices) (W r x : ℝ) : Prop where
  enoughW : battle C Bt H K ≤ W
  aperture : 2 * storeCost C ≤ r
  lends : stride H ≤ Heir.reach x
  stops : coarseCost C H * fiery G x H.L ≤ Bt.cash
  stubs : storeCost C * fiery G x H.L ≤ Bt.cash
  listens {c f : Side} (S : StepData c f) : S.patch=H → S.kernel=K → ∀ U : Config G f, (∀ i, G.chord (U i) ≤ tapCost C Bt H * fiery G x H.L) →
    (∀ y, uses S y U) ∧ ∀ k : S.Choices, ∀ i : Bond c, S.patch.usesBest S.kernel (S.connector U k.1 i)

theorem peaceful (C : Libretto G n) (Bt : Baton G) (H : Patch) (K : KernelChoices) (hk : H.Branches K G) (hW : battle C Bt H K ≤ W) (hr : 2*storeCost C ≤ r) : ∀ᶠ x in atTop, Peace C Bt H K W r x := by
  have h (Z : ℝ) : ∀ᶠ x in atTop, Z*fiery G x H.L ≤ Bt.cash := by
    simpa only [AnalyticNext.ConnectedActivity.Rates.allowance, AnalyticNext.ConnectedActivity.Rates.pieces,pow_zero,one_mul,pow_one] using
      (((AnalyticNext.ConnectedActivity.Rates.slow G H).const_mul Z).eventually (ge_mem_nhds (by simpa only [mul_zero] using! Bt.small : Z*0 < Bt.cash)))
  filter_upwards [h (coarseCost C H),h (storeCost C),Work.E01.radiusB_tendsto.eventually_ge_atTop (stride H), Aff.tap_open H K hk 1 1 zero_lt_one,
    (tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto).eventually_ge_atTop (tapCost C Bt H)] with x hC hh hx hA hR
  change tapCost C Bt H ≤ (radiusB x:ℝ) at hR
  refine ⟨hW,hr,by unfold Heir.reach; omega,hC,hh,fun S hS hK U hU => ?_⟩
  have he k i := hA S hS hK U k i (fun j _ => (hU j).trans (by rw [AnalyticNext.ConnectedActivity.Rates.allowance, AnalyticNext.ConnectedActivity.Rates.pieces,pow_one,pow_one]; gcongr; exact Work.E04.temp_nonneg _))
  unfold uses; exact ⟨fun y => hK.symm ▸ (he (Classical.ofNonempty : S.Choices) (y,0)).1,fun k i => hK.symm ▸ (he k i).2.1⟩

variable {E : Set (Site f)} {o : Site c} (a : Museum F x A X Y I) (U : Config G c → Config G f) (w : Config G c → Prices G I)
    (h : Plays C D P B Pt T x) (hV : Healthy P.threshold Y V) {Bt : Baton G} (hP : Peace C Bt S.patch S.kernel W r x)
    (hu : 0 < u) (hz : Guarded a E u (D.ε*B.threshold) (w V))

abbrev extendCalm (S : StepData c f) (g : Site c → G.El) (E : Set (Site f)) (U : Config G f) (e : Bond f) := if Needs E e then gauge (g ∘ S.ratio.parent) U e else 1
lemma calm_agrees (g : Site c → G.El) (U : Config G f) : Agrees E (extendCalm S g E U) (gauge (g ∘ S.ratio.parent) U) := fun _ h h' => if_pos ⟨h,h'⟩

lemma parent_reaches (o : Site c) {y : Site f} (hy : y ∈ frameUses S o) : separation o (S.ratio.parent y)+1 ≤ stride S.patch := by
  obtain ⟨b,hb,rfl⟩ := hy
  have hh := Work.E04.parent_separation S.ratio _ _ |>.trans (Nat.add_le_add_right (Work.E08.separation_box_add (S.ratio.embed o) (show b∈box _ from hb)) 1)
  rw [S.ratio.embed_parent] at hh; dsimp only; unfold stride; omega
lemma home_reaches {i : Bond c} {y : Site f} (hi : y ∈ predictorUses S i) : separation i.1 (S.ratio.parent y) ≤ stride S.patch := by
  rcases hi with h|h
  · have h := parent_reaches _ h; omega
  apply (separation_triangle _ (i.1+step i.2) _).trans ((Nat.add_le_add_right (Work.E03.sep_step i.1 i.2) _).trans _)
  rw [Nat.add_comm]; exact parent_reaches _ h

include a h hV hP hu hz
lemma leader (ho : S.ratio.embed o∈inspected X) (hE : E⊆ inspected X) (hr : ∀ y∈E, separation o (S.ratio.parent y) ≤ stride S.patch) : ∃ g : Site c → G.El,
    (∀ i : Bond c, separation o i.1 ≤ stride S.patch → G.chord (gauge g V i) ≤ Bt.cost * coarseCost C S.patch * B.threshold) ∧
    (∀ i, G.chord (extendCalm S g E (a.received k T q d u V (U V) (w V)) i) ≤ tapCost C Bt S.patch * B.threshold) := by
  have he := h.rehearsed.fiery_eq
  obtain ⟨g,hg⟩ := a.canvas _ ho hV h.space C.Z (by have := P.order_ge; have := h.rehearsed.test; omega) h.rehearsed.wire
  rw [S.ratio.embed_parent] at hg
  let v := Heir.crop o (Heir.reach x) g V
  let t := B.threshold; let K := coarseCost C S.patch; have ht := B.threshold_pos; change 0 < t at ht
  have hC := C.C_one; have hL : 0 < K := mul_pos (by positivity) (by unfold stride; positivity); have hB := Bt.large
  have hh (i : Bond c) (hi : separation o i.1 ≤ stride S.patch) : G.chord (gauge g V i) ≤ Bt.cost * K * t := by
    have h₀ : P.threshold ≤ 2*t := h.rehearsed.temp_eq.symm ▸ h.rehearsed.tensions.coarse
    have h₁ : ‖v i‖ ≤ K*t := (hg.size i (hi.trans hP.lends)).trans (le_trans (mul_le_mul
      (mul_le_mul_of_nonneg_left h₀ (by positivity : 0 ≤ C.C)) (show (1:ℝ)+separation o i.1 ≤ 1+stride S.patch by exact_mod_cast Nat.add_le_add_left hi 1) (by positivity) (by positivity)) (by unfold K coarseCost; rw [show Cube.fee C.Z=C.C from rfl]; nlinarith only))
    rw [hg.seen.self_of_nhds i (hi.trans hP.lends)]
    change G.chord (G.lieExp (v i) * 1) ≤ _; rw [mul_one]
    exact (Bt.pays _ (h₁.trans (by unfold K t; rw [he]; exact hP.stops))).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h₁ hB.le)
  let K' := storeCost C; have hK : 0<K' := storeCost_pos ..
  have h' : 0 ≤ tapCost C Bt S.patch * t := by unfold tapCost; change 0 ≤ Bt.cost*(K'+K)*t; positivity
  refine ⟨g,hh,fun i => ?_⟩
  unfold extendCalm; split; swap; · rw [G.chord_one]; exact h'
  next hi =>
  by_cases hT : i∈F.trunks
  · rw [Lattice.gauge,show a.received k T q d u V (U V) (w V) i=1 from F.on_tree _ ⟨i,hT⟩]; dsimp only [Function.comp_apply]; rw [F.trunk_internal hT]; simpa only [mul_one,mul_inv_cancel,G.chord_one] using h'
  let s : Active A x F := ⟨⟨i,hT⟩, a.admits (hE hi.1) (hE hi.2)⟩
  obtain ⟨j,hj⟩ := a.covers s (hE hi.1) (hE hi.2)
  have hj : a.address j=i := congr_arg (fun e : Active A x F => e.val.val) hj
  let L := G.adjoint ((g ∘ S.ratio.parent) i.1); let b := a.deposited k T q d u V (U V) (w V) (a.seat j)
  have h₁ : ‖L b‖ ≤ K'*t := (G.norm_adjoint ..).trans_le (displacement a U h hV hu.le _ (hz j (hj.symm ▸ hi)))
  have h₂ : G.chord (replica S.ratio (gauge g V) i) ≤ Bt.cost*K*t := by
    unfold replica; split; · rw [G.chord_one]; positivity
    exact hh _ (hr _ hi.1)
  have h₃ : gauge (g ∘ S.ratio.parent) (a.received k T q d u V (U V) (w V)) i = G.lieExp (L b)*replica S.ratio (gauge g V) i := by
    rw [← copied S.ratio S.patch.odd_side]; unfold Lattice.gauge L constantGauge; rw [station_release a U hj, exp_adjoint]; change _ * (G.lieExp b * _) * _ = _; group
  rw [h₃]; apply (G.chord_triangle ..).trans; have he := (Bt.pays _ (h₁.trans (by unfold K' t; rw [he]; exact hP.stubs))).trans (mul_le_mul_of_nonneg_left h₁ hB.le)
  change _ ≤ (Bt.cost*(K'+K))*t; linarith only [h₂,he]

omit hz
lemma frame_pass (o : Site c) (hE : frameUses S o ⊆ inspected X) (hz : Guarded a (frameUses S o) u (D.ε*B.threshold) (w V)) : uses S o (a.received k T q d u V (U V) (w V)) := by
  obtain ⟨g,-,hg⟩ := leader (k:=k) (d:=d) (q:=q) a U w h hV hP hu hz (hE (Push.GridApprox.window_home ..)) hE (fun y hy => le_trans (Nat.le_succ _) (parent_reaches o hy))
  rw [h.rehearsed.fiery_eq] at hg
  exact (uses_gauged ..).1 ((uses_same S o (calm_agrees g _)).1 ((hP.listens S rfl rfl _ hg).1 o))

lemma baton (e : Bond c) (hE : predictorUses S e ⊆ inspected X) (hz : Guarded a (predictorUses S e) u (D.ε*B.threshold) (w V)) : Conduct S k (a.received k T q d u V (U V) (w V)) V e (W*B.threshold/2) := by
  let Z := a.received k T q d u V (U V) (w V); let E := predictorUses S e; let t := B.threshold; let A' := tapCost C Bt S.patch; let F' := Vault.farePrice S.patch S.kernel
  obtain ⟨g,hg,hG⟩ := leader (k:=k) (q:=q) (d:=d) a U w h hV hP hu hz (hE (Or.inl (Push.GridApprox.window_home ..))) hE (fun y hy => home_reaches hy)
  have hz := hG; rw [h.rehearsed.fiery_eq] at hG; have hm := hP.listens S rfl rfl _ hG
  let Q := extendCalm S g E Z
  have hh := h.bulletin.priced; have hS : S.patch.Branches S.kernel G := hh.knobs.symm ▸ hh.kernel
  apply Conduct.ungauge hS (g:=g)
  apply Conduct.read hS (U:=Q) _ (calm_agrees g Z)
  have ht := B.threshold_pos; change 0<t at ht
  have ha := C.C_one
  have hA : 0≤4*A'*t := by have := Bt.large; unfold A' tapCost coarseCost; positivity [storeCost_pos C]
  refine ⟨fun x _ => hm.1 x, hm.2 k e, ?_⟩
  have hQ := Vault.prediction_good S Q k (4*A'*t) hA (fun i _ => show G.chord (Q i) ≤ _ from (hz i).trans (by change A'*t ≤ _; linarith only)) e
  apply (G.chord_triangle ..).trans_lt; rw [G.chord_inv]
  have hi := hg e (by simp : separation e.1 e.1 ≤ stride S.patch)
  have he := mul_le_mul_of_nonneg_right hP.enoughW ht.le
  unfold battle at he; change _ < W*t/2; linarith only [hQ,he,ht,hi]
end YM.PhysicalNext.JointLoad.Psalm
