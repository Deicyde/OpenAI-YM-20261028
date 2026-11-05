import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Licence
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Tariff

set_option warningAsError false

/-!
# Annulus payment in gaussian coordinates, with compulsory change costs

 typed on the sector (`Factor` for the exact relation with
`dyed`). Still a local, not volume statement; depends on the actual
compulsory guards; the tag and frozen counts and spectral bill paid at
fixed L. Long-range and postintegration effects AND the rest of the
local analytic comparisons are absolutely not included, see `owing`.
No step application unless the same prerequisites/prices in force.

`at_packet` charges also an extra coupon `(H,n)` with those terms
retained. It's valid with a local hypothesis on paired window charges
or, in `Payment` and `purchase` below, that part is actually bought
(with correct level time and V records). Correct flags on the fixed V
are necessary for use of `opaqueCost` to buy those; not an assumption
that the entire stored sector is realizable by a fine U. This s,V hold
means correct output-flag table, not all flags small. `Clearance`
allows overlapping/merged seeds. True charts and common coupling
reads supported, not asking for independent m or C after splitting.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus
open Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree
    YM.Push.SectorMeasure Oriented Exterior Bloch Next.SectorChange Set MeasureTheory Tariff
open YM.SectorNext.Remainder (coin)
open YM.SectorNext.Remainder.Affine
open YM.SectorNext.Remainder.Scales
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (T : Tube G S) (x w : ℝ) (V : Config G c) (A O : Stores S) (k : S.Choices)
    (F : Forest S.ratio) (D : ℕ) (p₀ q : Chi) (J : ChartRatio G) (d β : ℝ)
    (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))
    (Y : LinkArray G (Frozen A x F)) (z : Prices G (Active A x F))

theorem at_packet (hJ : LocalRatio J) {P : Teller G} (hP : P.Funds S T) (hS : 100*(1+radiusB x)≤c.val)
    (hD : 2≤D) {C E H κ : ℝ} {n : ℕ} (hE : 0≤E) (hH : 0≤H) (hw : 0<w)
    (hd : 0<d) (hr : 2*d<firstRadius G) (hl : 4*d<J.radius) (ht : Accepts S.patch P w C x)
    (hκ : PointCharge T x w κ) (he : C*fiery G x S.patch.L ≤ d)
    (hB : Ledger P S.patch.L w κ C (H+payroll S.patch J D E) (max 4 n) D x)
    (hb : β∈Set.Icc (y G S.patch.L x/2) (2*y G S.patch.L x))
    (ho : Clearance O A ((D+100)*radiusB x))
    (hx : ∀ i∈pairsAt O F D x, LocalLog.paired T x V A k F i ≤ E) :
    Real.exp (valuation O H n x G) * ‖packet T x w V A O k F D p₀ q J d β m Y z‖ ≤
      remaining O G x κ := by
  let a := m Y + coupling β • z
  let U := physical A F V Y (tape a)
  let X := Visits.near O D x; let N := openAt O A D x F
  let hm := releaseOn x w V A k F p₀ q J d β m Y z X N
  let Ls s := inner O D x s; let q₁ := LocalLog.write T x V A O k F D; let q₂ := quotaCharge x A F J β (freezeAt O A x F)
  let b := labor T x V A k F q d β m Y z Ls
  let a1 := valuation O H n x G
  change Real.exp a1 * ‖hm * Real.exp (b + q₁ + q₂)‖ ≤ _
  by_cases hy : hm=0
  · rw [hy,zero_mul,norm_zero,mul_zero]; exact (Real.exp_pos _).le
  have hI := hB.1
  have hA : 0 < fiery G x S.patch.L := Work.E09.temp_pos (x:=betaF G x S.patch.L) (zero_lt_one.trans hI)
  change jacob J q d N (tape a) * (border X A p₀ x w U V k * tagRate X k U) ≠ 0 at hy
  have hp s := suffices_for T x V O A F k q J d Y a D s w C rfl hS hP ht ho le_rfl hd hr he
    (left_ne_zero_of_mul hy)
    (posted O A p₀ D x w U V k hw hA (funds_branch hP) (right_ne_zero_of_mul hy) s)
  let h := payroll S.patch J D E; let K := max 4 n; let v₁ := valuation O (H+h) K x G
  let Q := rim O D x
  let q' s := selectFrom (Q s) A F x s
  let u := angle x V A F q d Y a
  let e := averaged (fun s => credits U V O Q q' T x k u s)
  have hh := (used U V O Q q' k u F A rfl hS hP β C (H+h) w κ D K hκ hB hb (show SliceSet S F U from
    fun i hi => F.on_tree _ ⟨i,hi⟩) (fun s => (hp s).1)).2
  have hn : ∀ s, debris T x V k A F q d Y a U s (Ls s)=credits U V O Q q' T x k u s := by
    obtain ⟨l₁,l₂,h1,-⟩ := hP.feeds
    exact fun s => core_match T x V k A F q d Y a U O s D h1 ht.1 hD ho (hp s).2
  let W := -κ/4*p G S.patch.L x^2*O.shares
  have hL : b ≤ W - v₁ := by
    change Real.exp (-β*e)≤ Real.exp (W - v₁) at hh
    have hi := Real.exp_le_exp.mp hh
    let f s := squares T x V k A F q d Y (m Y) s (Ls s)
    have hz : 0 ≤ averaged f := le_trans (le_of_eq (av_const 0).symm) (av_mono fun _ => squares_nonneg ..)
    have hU : averaged (fun s => debris T x V k A F q d Y a U s (Ls s)) = e := congr_arg averaged (funext hn)
    change -β*_ - averaged f / (coupling β)^2 ≤ _ ; rw [hU]
    apply le_trans _ hi; exact sub_le_self _ (div_nonneg hz (sq_nonneg _))
  let w₁ := streets (D+100) x O * Real.log (Fintype.card S.patch.FrameTag:ℝ)+Fintype.card Axis *
    streets (D+101) x O *Real.log (Fintype.card S.patch.Points:ℝ)
  have hΓ := (funds T x V A O F D J hJ k (β:=β) ht.2.1 hB.1.le hb hE hx)
  have hΓ' : a1+(w₁+q₁+q₂)≤v₁ := (add_le_add_right hΓ _).trans (accumulated O H h n x hH
    (payroll_nn S.patch J D hE) hI.le)
  have htJ : ‖hm‖ ≤ Real.exp w₁ := by
    obtain ⟨ha,hX⟩ := jacob_range J q d N (tape a) hJ hd hl
    obtain ⟨hi,hY⟩ := border_range X A p₀ x w U V k
    have hr : 0 ≤ tagRate X k U := (rate_cost ..).1
    change ‖jacob J q d N (tape a)*(border X A p₀ x w U V k*tagRate X k U)‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg ha (mul_nonneg hi hr)), ← mul_assoc]
    apply (mul_le_of_le_one_left hr ((mul_le_mul hX hY hi zero_le_one).trans (by simp))).trans
    exact tag x O k D U ht.2.1
  rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp a1 * (Real.exp w₁ * Real.exp (b+q₁+q₂)) := by gcongr
    _ ≤ remaining O G x κ := by
      rw [← Real.exp_add, ← Real.exp_add]; change Real.exp _ ≤ Real.exp W
      exact Real.exp_monotone (by linarith only [hL,hΓ'])

section price
variable (Q : Patch) (P : Teller G) (J : ChartRatio G) (w κ H : ℝ) (n D : ℕ) (a x : ℝ)

/-- Same-calendar post-L affordability of the local factors. Positivity of
constants prerequisites stated separately, especially κ. This request is
*before* naming a wait, history or instance R -- use its estimates only
at/above the purchased altitudes. Includes spectral log pairing. Correct
flags, arbitrary tagged sectors not necessarily realizable. -/
def Payment :=
    let d := a * fiery G x Q.L
    1<y G Q.L x ∧ 120≤radiusB x ∧ 0<d ∧ 2*d<firstRadius G ∧ 4*d<J.radius ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=Q → 100*(1+radiusB x)≤c.val →
    P.Funds S T → PointCharge T x w κ →
    ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c) (O : Stores S),
      Clearance O A ((D+100)*radiusB x) → A.flags=RG.flags (temp x) V →
      ∀ (p q : Chi) (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))
        (Y : LinkArray G (Frozen A x F)) (z : Prices G (Active A x F)) (β : ℝ),
        β ∈ Icc (y G Q.L x/2) (2*y G Q.L x) →
        Real.exp (valuation O H n x G)*‖packet T x w V A O k F D p q J d β m Y z‖ ≤ remaining O G x κ

open Filter

lemma pay (w : ℝ) (Q : Patch) (P : Teller G) (J : ChartRatio G) (hJ : LocalRatio J)
    (hp : Q.Branches P.bind G) (hw : 0<w) :
    ∃ a₀ : ℝ, 0<a₀ ∧ ∀ a ≥ a₀, ∀ κ : ℝ, 0<κ → ∀ H : ℝ, 0≤H → ∀ (n D : ℕ),2≤D →
    ∀ᶠ x : ℝ in atTop, Payment Q P J w κ H n D a x := by
  obtain ⟨C,hC,h⟩ := forecasts Q P w hw hp
  obtain ⟨E,hE,he⟩ := LocalLog.solvent G Q P hp
  have hz := zero_lt_one.trans_le hC
  refine ⟨C,hz,fun a ha κ hκ H hH n D hD => ?_⟩
  have hh : Tendsto (fun x : ℝ => a*fiery G x Q.L) atTop (𝓝 0) := by
    have hv := (tally_g G Q.L 0 1).const_mul a; rw [mul_zero] at hv
    exact hv.congr fun x => by rw [fi]; ring
  filter_upwards [h,he,YM.SectorNext.Remainder.Affine.authorize P Q.L w κ C (H+payroll Q J D E) (max 4 n) D hw hκ,
    Work.E01.radiusB_tendsto.eventually_ge_atTop 120,
    hh.eventually (gt_mem_nhds (show (0:ℝ)< min (firstRadius G/2) (J.radius / 4) by
      have hp := first_pos G; have hd := hJ.patch; positivity))] with x hx he hL hB hJ'
  have hy := hL.1
  have hl : 0 < fiery G x Q.L := Work.E09.temp_pos (x:=betaF G x Q.L) (by exact zero_lt_one.trans hy)
  unfold Payment
  intro d
  change d < _ at hJ'
  obtain ⟨hi,hf⟩ := lt_min_iff.mp hJ'
  have hd : 0<d := mul_pos (hz.trans_le ha) hl
  have hi : 2*d<firstRadius G := by linarith
  have hf : 4*d<J.radius := by linarith
  refine ⟨hy,hB,hd,hi,hf,fun {c f} S T hQ hy hP hF A F k V O ho hV p q m Y z β hβ => ?_⟩
  apply at_packet T x w V A O k F D p q J d β m Y z hJ hP hy hD (C:=C) hE hH hw hd hi hf (by rw [hQ]; exact hx) hF
    (by rw [hQ]; exact mul_le_mul_of_nonneg_right ha hl.le) (by rw [hQ]; exact hL) (by rw [hQ]; exact hβ) ho
  exact fun i _ => le_trans (le_abs_self _) (he S T hQ hy hP A F k V hV i)


end price
end YM.AnalyticBridge.Annulus
