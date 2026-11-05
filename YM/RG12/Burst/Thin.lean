import YM.RG12.Burst.Weight
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Sparks
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy.Charity.RG12
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters Blaze.March
variable (M:Leaf R) (H:Cash W x μ L Q o C T R)
    {s Y A b B C' v d q u r:ℝ}{j n:ℕ}{χ:Chi} (N: Captain H j q d v Y A b r B C' n χ)
local notation "d0" => jewelDebt M Q L x
local notation "Z" => N.conduit
local notation "cR" => Q.costs L μ R.beta x q

-- rescaled ingress readiness. Before θ.W. uniform in call-world.
def white (Q : ConnectedActivityE6.Target G P)(L:Side)(μ x s:ℝ)(n:ℕ):ℝ:=Reserves.extract Q.ε n 0 0 * Reserves.treeYield (s*(Q.costs L μ 1 x 0).rootHit) (1/2) 0
def black (Q : ConnectedActivityE6.Target G P)(L:Side)(μ x s:ℝ)(n:ℕ):ℝ:=Reserves.extract Q.ε n 0 0 * Reserves.treeYield (s*(swing Q L μ 1 x 0).rootHit) (1/2) 0
set_option quotPrecheck false
lemma meant_hit (hs:0<s) (hp:degreePrice (radiusB x) (s*(Q.costs L μ 1 x 0).rootHit) Q.δ≤1/2)(z : ℝ)(hz : z≤Q.exp) : Ac.Hit H.smallAt (radiusB x) (fun p=> s^p.val.card * (Z).meant p.val n) z (white Q L μ x s n):=by
  have hh:= Coupons.collect S Q.halo (radiusB x) (Q.costs L μ R.beta x q) H.birth (Z).flair (ConnectedActivityE6.lengths T R) _ (Z).lives (Z).accrues hs hp (by norm_num) 0 n 0 0
  rw [Nat.cast_zero,mul_zero] at hh
  change Ac.Hit H.unionP (radiusB x) (fun p=> s^p.card * N.conduit.meant p n) Q.exp _ at hh
  intro i; have ht:= budget_pull (fun i:H.ThinP=>Subtype.val i) Subtype.val_injective (hh i)
  refine budget_mono ht (fun p=>?_) (fun p=>?_)
  · split; exact mul_nonneg (mul_nonneg (pow_nonneg hs.le _) ((Z).meant_nonneg _ _)) (Real.exp_pos _).le; rfl
  split
  next h=> dsimp only; rw [if_pos (show i∈H.unionP p.val from h)]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg _))) (mul_nonneg (pow_nonneg hs.le _) ((Z).meant_nonneg _ _))
  next h=> exact ht.1 _
lemma narrow (hs:0<s) (hp:degreePrice (radiusB x) (s*(swing Q L μ 1 x 0).rootHit) Q.δ≤1/2)(hv:Bikes Q L μ x a E B j n)(hF:foam Q L) (z : ℝ)(hz : z≤Q.exp) : Ac.Hit H.smallAt (radiusB x) (fun p=> s^p.val.card * persona M H q N.conduit.flair 0 n 0 p.val) z (black Q L μ x s n):=by
   have he:=H.laws.data.funds.length_eq; have hW : R.p.B≤2*radiusB x:=by rw [H.laws.intake.sizes,he]; exact hv.covers
   let b:= swing Q L μ R.beta x q; let g:=colly (Z).flair M Q L x; let h:=ConnectedActivityE6.lengths T R; let p:=steamP S (Q.costs L μ R.beta x q); let k:= Mixed.selected S Q.halo (radiusB x) b H.birth g h p 0 n 0 0
   have hu:= (Z).accrues; have hb:b.Buy S.patch.L Q.halo (radiusB x) := he.symm ▸ hv.rev _ _ (he ▸ (Z).lives)
   have H':= coco M H hF hW (Z).flair p q hu
   have hh:=Coupons.collect S Q.halo (radiusB x) b H.birth g h p hb H' hs hp (by norm_num) 0 n 0 0
   rw [Nat.cast_zero,mul_zero] at hh
   change Ac.Hit H.unionP (radiusB x) (fun p=> s^p.card * k p) Q.exp _ at hh
   have h0(i):0≤ persona M H q N.conduit.flair 0 n 0 i:= earned M H q _ (Z).fares 0 n 0 _
   have hi:=Push.AbsoluteSums.Labels.raise_prices H.unionP (radiusB x) (fun i=>mul_nonneg (pow_nonneg hs.le i.card) (h0 i)) hh (fun i=>by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs.le i.card); unfold k persona Mixed.selected; by_cases hx : H.ticketsP 0 0 0 i
      · rw [if_pos (show Allowed S Q.halo (radiusB x) b H.birth h 0 0 0 i from hx)]; split_ifs; exact le_rfl
        exact Mixed.zero_le_price S Q.halo (radiusB x) b H.birth g h p hb H' n i
      rw [if_neg (show ¬Allowed S Q.halo (radiusB x) b H.birth h 0 0 0 i from hx), if_neg (show ¬(H.ticketsP 0 0 0 i∧ M.turn.badge S ∈ i) from fun h=>hx h.1)])
   intro i; have ht:=budget_pull (fun i:H.ThinP=>Subtype.val i) Subtype.val_injective (hi i)
   refine budget_mono ht (fun p=>?_) (fun p=>?_)
   · split; exact mul_nonneg (mul_nonneg (pow_nonneg hs.le _) (h0 _)) (Real.exp_pos _).le; rfl
   split
   next h=> dsimp only; rw [if_pos (show i∈H.unionP _ from h)]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg _))) (mul_nonneg (pow_nonneg hs.le _) (h0 _))
   next h=> exact ht.1 _

def value10 (Q : ConnectedActivityE6.Target G P)(L:Side)(μ x s B:ℝ)(j n:ℕ):ℝ:=2^(j+2)*(B*(white Q L μ x s n)+2*(B*(black Q L μ x s n)))
local notation "X₀" => value10 Q L μ x s B j n
def gold (p:H.ThinP):=s^p.val.card*zoe M H N p
lemma golden10 (hs:0<s) (h1:degreePrice (radiusB x) (s*(Q.costs L μ 1 x 0).rootHit) Q.δ≤1/2)
    (h2:degreePrice (radiusB x) (s*(swing Q L μ 1 x 0).rootHit) Q.δ≤1/2)(hv:Bikes Q L μ x a E B j n)(hF:foam Q L) : Ac.Hit H.smallAt (radiusB x) (gold M H N (s:=s)) (a+E+E) X₀:=by
   intro i
   convert! budget_scale (show 0≤ (2:ℝ)^(j+2) from by positivity) (budget_plus (budget_scale N.balance (meant_hit H N hs h1 _ hv.win i)) (budget_scale zero_le_two (budget_scale N.balance (narrow M H N hs h2 hv hF _ hv.win i)))) using 2
   rename_i p; dsimp only; split
   · unfold gold zoe momentS sip; ring
   simp
-- Want B>0 of actual Commander. Don't require! Add post floater d0 small even if not positive. Better add root earned small (goal) once.
local notation "t!" => Q.goal L x+ X₀
lemma skill (hs:0<s) (h1:degreePrice (radiusB x) (s*(Q.costs L μ 1 x 0).rootHit) Q.δ≤1/2)
    (h2:degreePrice (radiusB x) (s*(swing Q L μ 1 x 0).rootHit) Q.δ≤1/2)(hv:Bikes Q L μ x a E B j n)(hF:foam Q L)(h3:degreePrice (radiusB x) t! E≤1/2): Ready H.smallAt (radiusB x) (gold M H N (s:=s)) (a+E) t! E (1/2):=by
  have hh:=golden10 M H N hs h1 h2 hv hF
  exact ⟨add_pos_of_pos_of_nonneg (arable H) (budget_nonneg (hh 0)),hv.allow,h3,by norm_num,fun i=> mul_nonneg (pow_nonneg hs.le i.val.card) (rises M H N i),fun i=>budget_loosen (hh i) (le_add_of_nonneg_left (arable H).le)⟩
/- Keep coupling penalty *multiplicative*, also throughout taking algebraic log. Thus
can handle diagrams having MANY constituents INSIDE the few outer clusters. -/
def hue (p:H.fragrances):ℕ:= ∑ i, (p.2 i).val.card
lemma beauty (p:H.fragrances) : clusters H.seam (gold M H N (s:=s)) p.2= s ^ hue H p * oval M H N p:=by
   unfold hue oval clusters gold; rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; ring
lemma ink (hv:Bikes Q L μ x a E B j n)(hr: Ready H.smallAt (radiusB x) (gold M H N (s:=s)) (a+E) t! E (1/2)):
    Ac.Hit (fun i:H.fragrances=> H.bookFoot (.inr i)) (radiusB x) (fun i=> s ^ hue H i * oval M H N i) (a+E) ((t!) * (1-(1/2):ℝ)⁻¹):=by
    intro i
    have h:=log_hit_tail H.seam H.smallAt (radiusB x) H.testS hr (add_nonneg hv.posts hv.allow.le) 0 i; rw [pow_zero,mul_one] at h
    convert! h using 2; rename_i p; dsimp only
    simp_rw [← beauty M H N (p:=p)]
    unfold currency; change (if i∈unionOf H.smallAt p.2 then _ else _)=(if _ then _ else _); simp; rfl
end YM.PhysicalNext.Repeat.Daisy.Charity.RG12
