import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Gliss

/-! # Upgrade actual turning-parent derivative bill by the snare profiles.
Underlying parent (WITHOUT telescope Ξ) and Γ's raw/unmasked costs are a
separate procurement; we give also the profile-only part of Γ's invoice.
Same threshold, exact shifted & held motion rates, all numbers of keys,
no factor depending on #carriers charged per undifferentiated choice. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm
open Function Filter Set Lattice Wilson RG Tree Pressure Precision Next Next.SectorChange Wisps Bid
   Push.SectorMeasure ProjectorNext.Equivariance Heir AnalyticBridge.LocalGaussian Extra.Iteration
   Spot Spot.Programme Notice
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {d : Desk G S} {u : Spot d}
    {ι : Type} [Fintype ι] {X X' : Support c} {Y : Support f} {N m : ℕ} {D : Record} {V : Config G c}
    {H R K α β γ : Type} {l : Viewport u X H R K} {ds : u.Slices} {b : Finset ℕ} {q : Programme ds b} {n : q.Run α β γ}
    {A' : Notice l} {s : Seats l n} {v : Charges} {B' : Reading A' n} {o : Site c} {L t W θ : ℝ}
    {M : Income α β γ (H⊕R)} {p : Reel G H R K}

variable (σ : ι ↪ (H⊕R)) (A' p) [Fintype H] [Fintype R]
def scaleRead (W : Config G c) : Prices G ι := A'.imprint W p ∘ Prod.map σ id
abbrev keyBill (v : Charges) (l : Viewport u X H R K) (o : Site c) (L : ℝ) (N : ℕ) : H⊕R → ℝ := Sum.elim
    (fun i => ∑ j : G.ColorIndex, |motionBill v l o L N (i,j)|) (fun _ => 0)
omit [Fintype H] [Fintype R] in
lemma keyBill_nn (i : H⊕R) : 0 ≤ keyBill v l o L N i := by cases i <;> first | exact Finset.sum_nonneg (fun _ _=> abs_nonneg _) | exact le_rfl
variable {A' p}
    (hs : Pose B' s V p) {ok : u.ActiveKey → Prop} (hv : ∀ i,ok (l.read i)) (h : Part ok v d.radius d.tube u.k V d.out N d.broadCut d.g)
    (hT : Studio d.chart t N L W) (hh : Needed l t V p)
include hs hv h hT hh
lemma pulses (j : Component G H R) : Charge (d.out.dirBound o) N V (keyBill v l o L N j.1) (A'.movement p j) := by
  rcases j with ⟨i|i,b⟩
  · exact (hs.motions_part hv h hT hh i b).radius ((le_abs_self _).trans (Finset.single_le_sum (f:=fun j => |motionBill v l o L N (i,j)|) (fun j _ => abs_nonneg _) (Finset.mem_univ b)))
  exact A'.vacated p i b ▸ Charge.freeze (p.2.1 (i,b)) (le_refl 0)

omit [Fintype ι] in
lemma scale_cont : ContinuousAt (scaleRead A' p σ) V := continuousAt_pi.mpr (fun i => chart_continuousAt _
    ((pulses (o:=0) hs hv h hT hh (σ i.1,i.2)).smooth.continuousAt))
variable (hG : Gliss D d N)
include hG
lemma snare_sold (i : ι) : let D₀ := d.out.dirBound o (G:=G); let r := keyBill v l o L N (σ i); let f := fun W => Pitch.snare D d (scaleRead A' p σ W) i
    Ticket D₀ N V 1 r f ∧ Ticket D₀ N V 1 r (1-f) := by
  exact hG _ le_rfl V _ _ _ (keyBill_nn _) (fun b => pulses hs hv h hT hh (σ i,b))

variable (s M v o L N) [Fintype γ]
omit hs hv h hT hh hG in
lemma total_pulses : ∑ i : ι,keyBill v l o L N (σ i) ≤ totalBill s v M o L N := by
  rw [← Finset.sum_image σ.injective.injOn]; refine le_trans (b:=∑ i,keyBill v l o L N i) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>keyBill_nn _)) ?_
  unfold totalBill; rw [Fintype.sum_sum_type]
  have ht := abs_nonneg M.royalty
  have hm : 0 ≤ ∑ i,M.wages i := Finset.sum_nonneg fun i _=>M.wages_nn i
  have hh : 0 ≤ ∑ j:s.big,s.charge o (d.out.power*N) j := Finset.sum_nonneg fun i _=>(s.charge_pos ..).le
  rw [Fintype.sum_prod_type]; change ((∑ i,∑ j, |motionBill v l o L N (i,j)|) + ∑ _ : R,(0:ℝ)) ≤ _; simp only [Finset.sum_const_zero]; linarith only [ht,hm,hh]
variable {s M v o L N}
omit [Fintype γ] in
lemma taper_paid (i : Fin m ↪ ι) (j : Fin m) : let D₀ := d.out.dirBound o (G:=G); let r := fun j => keyBill v l o L N (σ (i j)); let f := fun W j => Pitch.snare D d (scaleRead A' p σ W) (i j)
    Ticket D₀ N V 1 (∑ j,r j) (fun W => ∏ j' : Fin m, if j' < j then f W j' else (1:ℝ)) := by
  intro D₀ r f
  let g t : Config G c → ℝ := if t<j then fun W=>f W t else 1
  have he (t : Fin m) (_ : t∈Finset.univ) : Ticket D₀ N V 1 (r t) (g t) := by
    unfold g; split; exact (snare_sold σ hs hv h hT hh hG _).1
    exact (show Ticket D₀ N V ‖(1:ℝ)‖ (r t) 1 from Ticket.pure (keyBill_nn _) 1) |>.mono (by simp) le_rfl
  convert Ticket.stack he using 1
  · simp
  ext W; simp only [Finset.prod_apply]; exact Finset.prod_congr rfl (fun k _ => by unfold g; split <;> rfl)

lemma peeled_jet (i : Fin m ↪ ι) (j : Fin m) {w : ℝ} {g : Config G c→ℝ} (hw : Ticket (d.out.dirBound o) N V w (totalBill s v M o L N * Moments.powers (A'.imprint V p) ^ (max 1 M.plan)) g) :
    Ticket (d.out.dirBound o) N V w (Growth M s v o L N (A'.imprint V p)) (fun W => peels (Pitch.snare D d (scaleRead A' p σ W) ∘ i) j*g W) := by
  have hh := ((taper_paid (o:=o) σ hs hv h hT hh hG i j).mul (snare_sold σ hs hv h hT hh hG (i j)).2).mul hw
  change Ticket _ _ _ _ _ (fun x => (∏ i' : Fin m, if i' < j then Pitch.snare D d _ (i i') else 1)*(1-Pitch.snare D d _ (i j))*g x)
  apply hh.mono (by simp)
  let r j := keyBill v l o L N (σ (i j)); let Y := totalBill s v M o L N; let R := Moments.powers (A'.imprint V p) ^ (max 1 M.plan)
  change (∑ k,r k)+r j+Y*R ≤ 3*Y*R
  have hs : ∑ k,r k ≤ Y := total_pulses N s v o L M (i.trans σ)
  have hr := Finset.single_le_sum (s:=Finset.univ) (f:=r) (fun k _=> keyBill_nn _) (Finset.mem_univ j) |>.trans hs
  have h := le_mul_of_one_le_right ((keyBill_nn _).trans hr : 0≤Y) (show 1 ≤ R from one_le_pow₀ (Moments.grows _))
  linarith only [h,hr,hs]

 -- prod
end YM.PhysicalNext.JointLoad.Psalm
