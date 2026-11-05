import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Amass
import YM.MergeProof.TeamSeries
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
namespace Team
variable (M : Team R) (X : Coat T F) (k:Finset ℕ)
def tithe (k : Finset ℕ) (W a : ℝ) (Ñ : ChartRatio G) (m : ℕ) (p : Molecule S):= ∫ i,M.into X W a Ñ k m p i ∂((F.order G).prod X.dice)
def hike (k : Finset ℕ) (W a : ℝ) (Ñ : ChartRatio G) (m : ℕ) (p : Molecule S):=if X.approve k R then M.tithe X k W a Ñ m p else 0

def fare (A : Stores S) (l : S.Choices) (p : Molecule S):=
    let X':= (Matter.preps X A).taggedL l
    X'.tribute R Q.table * M.hike X' (Matter.own p) W o.a Q.table Q.halo p
-- Main no-shadow insurance. from Tilt
variable (H:Cash W X.x μ L Q o C T R) (hk:X.width=o.K)
include H hk
lemma tokenRah (ha:X.manifest) (Y : Finset (Stores S)) (hp: Layout X.seeds Q.halo X.B Y) (ht: Contract.sealed R k):
    (∫ u,M.realP X (X.shifted u) k W ∂X.stages) = X.tribute R Q.table*∫ z,M.salary X k W o.a Q.table Y z ∂X.dice:=by
  let g (z) := ENNReal.ofReal (X.thetaRef z)
  have hd : X.dice = volume.withDensity g := Poll.sweep_pdf (H.laws.data.localP F X rfl hk ha).sails.fullC
  have hg : Measurable g := by unfold g thetaRef dotProduct; fun_prop
  rw [X.seatPTeam M H hk k, hd, integral_withDensity_eq_integral_toReal_smul hg (ae_of_all _ fun _=> ENNReal.ofReal_lt_top), ← integral_const_mul]
  apply integral_congr_ae; filter_upwards with z
  rw [M.approved X k H ha hk z hp ht]; unfold g tribute; rw [ENNReal.toReal_ofReal (show 0≤ X.thetaRef _ by unfold thetaRef bell; positivity),smul_eq_mul]; ring

lemma troops (Y : Finset (Stores S)) (hp : Layout X.seeds Q.halo X.B Y):
    HasSum (fun l => X.tribute R Q.table * M.hike X k W o.a Q.table Q.halo (issue Y k l)) (∫ i,M.realP X i k W ∂F.order G):=by
  have h:= H.laws.data; have hr:= H.laws.intake
  by_cases hh:X.approve k R
  · simp_rw [hike,if_pos hh]; obtain ⟨hL,hA⟩:= M.tithes X k H hk hh.1 Y hp
    convert! hA.mul_left (X.tribute R Q.table) using 1
    rw [X.shore_touchTeam M k hr h.W_pos, integral_prod _ hL, ← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall (fun i=> M.tokenRah (X.wrapY i) k H hk hh.1 Y hp hh.2.1))
  have he i : M.realP X i k W=0 := by by_contra hn; exact hh (M.exterior X k hr h.W_pos i hn)
  simp_rw [he,hike,if_neg hh, integral_zero,mul_zero]; exact hasSum_zero
lemma yoke (p : Molecule S) : ‖M.hike X k W o.a Q.table Q.halo p‖ ≤ crowns H.text M.weight (M.signs S) p:=by
  unfold hike crowns; split_ifs with h h' h'
  · exact (norm_integral_le_integral_norm _).trans (by simpa only [if_pos h'] using (M.tip X k H hk h.1 p).2.2)
  · exact (norm_integral_le_integral_norm _).trans (by simpa only [if_neg h'] using (M.tip X k H hk h.1 p).2.2)
  · rw [norm_zero]; exact mul_nonneg M.profit (prod_nonneg fun i _=> H.positive i)
  rw [norm_zero]

lemma brew (j : Stores S) (k : S.Choices):
    let Y := (preps X j).taggedL k
    HasSum (fun i : Finset ℕ × ListsAt c f => fare (o:=o) (Q:=Q) M X j k (crew S Q.halo X.B (j,i)))
      (∫ i, Y.χ.distribute j Y.x W (F.drape i) k X.V * (taggedKernel S R.beta k (F.drape i) X.V * M.cicada (F.drape i)) ∂ F.order G):=by
  intro Y; let V:= Layout.rolls j Q.halo X.B
  let a(u:Finset ℕ × ListsAt c f):= crew S Q.halo X.B (j,u)
  let g (u):=fare (o:=o) (Q:=Q) M X j k (a u)
  have hu (i):g i=Y.tribute R Q.table * M.hike Y i.1 W o.a Q.table Q.halo (issue V i.1 i.2):=by
    have hv : Matter.own (a i)=i.1:= congr_arg (fun i : Packed S=> i.2.1) (deposit (j,i))
    unfold g fare; dsimp only; rw [hv]; rfl
  have hf: Summable H.text:= Summable.sum _ (hasSum_fintype _).summable (budgets_arr H)
  have hp: Summable g:= by
    apply Summable.of_norm_bounded (g:=fun t=> ‖Y.tribute R Q.table‖ * crowns H.text M.weight (M.signs S) (a t))
    · apply Summable.mul_left; apply (crowns_has _ _ hf H.positive).comp_injective
      intro t u (h:a t=a u); apply congr_arg (f:=fun i: Packed S=> i.2) (show ( (j,t) : Packed S)=(j,u) from ((deposit _).symm.trans ((congr_arg obtainBack h).trans (deposit _)))) -- exact
    intro i; rw [hu,norm_mul]; exact mul_le_mul_of_nonneg_left (M.yoke Y _ H hk _) (norm_nonneg _)
  change HasSum g _; convert! hp.hasSum using 1; rw [hp.tsum_prod]; simp_rw [hu, (M.troops Y _ H hk V (Layout.enlists j Q.halo X.B)).tsum_eq]; exact ((M.world Y H.laws.intake H.laws.data.W_pos).2.tsum_eq).symm
omit H hk in
def bourbon (W a:ℝ)(Ñ:ChartRatio G) (l : ℕ) (p : Molecule S):=
    let Y:= preps X (roster p)
    if Y.approve (Matter.own p) R∧ Layout (roster p) l X.B p.toLeft then likely (fun k=> M.tithe (Y.taggedL k) (Matter.own p) W a Ñ l p) else 0
lemma success : HasSum (fun i:Molecule S=> overhead X R Q.table * M.bourbon X W o.a Q.table Q.halo i) (S.push R.beta M.cicada X.V):=by
  let V:= crew S Q.halo X.B
  let f i:= overhead X R Q.table * M.bourbon X W o.a Q.table Q.halo i; change HasSum f _; have hv: Injective V:=LeftInverse.injective (show LeftInverse obtainBack V from deposit)
  apply (hv.hasSum_iff (f:=f) ?_).1
  · rw [M.posted X H.laws.intake H.laws.data.W_pos]; apply Raw.finite_start; intro Y
    refine (hasSum_sum (s:=univ) (fun i _=> M.brew X H hk Y i)).congr_fun ?_
    intro t; let u:= V (Y,t); let Z:= preps X Y; let p:= overhead X R Q.table; let b:ℝ:= Fintype.card S.Choices
    have hx: roster u=Y:= congr_arg Prod.fst (deposit (Y,t))
    have ht:Layout Y Q.halo X.B u.toLeft:= by rw [show u.toLeft=Layout.rolls Y Q.halo X.B from toLeft_disjSum ..]; exact Layout.enlists ..
    change overhead _ _ _ * M.bourbon X W o.a Q.table Q.halo u = ∑ i:S.Choices,fare (o:=o) (Q:=Q) M X Y i u
    unfold bourbon; rw [hx]; dsimp only; split
    next h =>
      have hv i : (Z.taggedL i).tribute R Q.table=b⁻¹*p:=by rw [← show overhead _ R Q.table=p from visitsM X Y i Q.table R]; unfold b overhead tribute; ring
      have hp i: fare (o:=o) (Q:=Q) M X Y i u= (b⁻¹*p)*M.tithe (Z.taggedL i) (Matter.own u) W o.a Q.table Q.halo u:=by
        unfold fare hike; dsimp only; rw [show ((preps X Y).taggedL i).tribute _ _= _ from hv i, if_pos (show (Z.taggedL i).approve _ _ from h.1)]
      simp_rw [hp,← Finset.mul_sum]; unfold likely b p Z; ring
    next h=>
      rw [mul_zero]; symm; refine Finset.sum_eq_zero fun k _=> ?_; unfold fare hike; dsimp only; rw [if_neg (show ¬ (Z.taggedL k).approve (Matter.own u) R from fun hl=>h ⟨hl,ht⟩),mul_zero]
  intro i hi; unfold f bourbon; dsimp only; rw [if_neg (fun h=> hi ⟨_, recovery h.2⟩), mul_zero]
end Team
end YM.PhysicalNext.Repeat.Lotus
