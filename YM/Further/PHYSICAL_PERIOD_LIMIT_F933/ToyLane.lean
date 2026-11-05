import YM.Extra.ITERATION_NO_LOSS.MarkerRoom
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.WardBlank
import YM.Next.ROTATIONS.GapTest
import YM.Progress.DIRECTED_RECIPE.Deploy
import YM.Push.FINITE_DETECTION.Low

/-!
# Produce full marked Sphere & Wire purchases, at low weight for any based
source C on this route

θ powers, cameras etc aren't necessary here, but don't waive era forecasting
 for the other jobs; this purchase doesn't re-query. High offer usable separately.
Outside low range no claim of attainment from this trivial field; warning:
other Physics clients can't switch branches after using it. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Toy
open Function Set Matrix MeasureTheory Filter RG Wilson Lattice Precision Pressure Supply Bid Craft Tree Bloch
    Labels Source Org Input Marker Overlay Next.Extract Extraction Cells Push.Common
    Push.Corrected Endpoint Stock Mix WardBin.Crest
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge}
section constants
variable {V : Type} [Fintype V] [DecidableEq V] {n : Side} {P : Rep G n} (i : V) (s : V→Site n) (a : V→ℂ)

-- adding actual constant units at all origins, and all marker sums still costed above gas
abbrev upright (s : V→Site n) (a : V→ℂ) : Bands (census V) P := {Tin.freeBand (W:=census V) (R:=P) s i with units := a}

theorem additions (U : Config G n) {a₀ w : ℝ} (H : (P.activities).Valid P.p a₀ w) (q : (census V).Mode) :
    ((upright (P:=P) i s a).density U).part q = (P.eval U:ℂ) * ∏ j∈q.val,a j := by
  let E := Tin.freeBand (W:=census V) (R:=P) s i
  let Z := upright (P:=P) i s a
  have ht : ∀ j, E.ray j U = 0 := by
    intro j
    by_cases h : Healthy P.p.threshold (E.support j) U
    · rw [Bands.ray,masked_eq _ _ _ _ h]; exact Poly.send_zero _
    rw [Bands.ray,masked_ne _ _ _ _ h]; exact Poly.send_zero _
  have hh : E.extra U=0 := by
    unfold Bands.extra; simp only [ht,E,Pi.zero_apply,Poly.send_zero,Finset.sum_const_zero,tsum_zero,add_zero]
  have hZ : Z.extra U = ∑ j:V,WardBin.Lambda.fuse j (a j) := by
    unfold Bands.extra
    rw [show Z.ray=E.ray from rfl,show (∑' j,E.ray j U)=0 from by simp [ht],add_zero]; rfl
  have hg := Tin.none (W:=census V) i s U H
  unfold Bands.density at hg ⊢
  have hp : Poly.pass (0 : Poly (census V))=1 := by
    unfold Poly.pass; rw [Finset.sum_eq_single 0]; simp
    · intro b _ h; simp [zero_pow h]
    simp
  rw [hh,hp,one_mul] at hg
  change ((_:ℂ) • (Poly.pass (Z.extra U)*E.cluster U)).part _=_
  rw [hZ,WardBin.Lambda.passion,mul_comm,← smul_mul_assoc,hg, ← show (Poly.bead (census V) (P.eval U:ℂ))=Poly.send (census V).quiet (P.eval U:ℂ) from rfl,
    Poly.product_bead,Poly.part_smul,WardBin.Lambda.expend]

lemma incidental (w : ℝ) (h : ∀ j, w*‖a j‖ ≤ 1) (e : ∀ u v : V, u≠v → 8 ≤ P.p.B ∧ P.p.B * P.p.B ≤ separation (s u) (s v)) :
    Stubs.Holds (upright (P:=P) i s a) w := by
  let R := upright (P:=P) i s a
  refine ⟨h,⟨fun _=> Finset.singleton_nonempty _,fun _ _ _=>Finset.mem_univ _,fun _=> (WardBin.zeroPrice P.p _ (0:Site _)).1,
    fun _ _=> Finset.singleton_nonempty _,fun _ _ hh=> (hh rfl).elim, fun _ _ _ _ _ _=>rfl,fun _ _ U hh=>(hh rfl).elim, fun _ _=>measurable_const,fun _ _ _ _=>rfl⟩,e,?_⟩
  let X : Stubs R :=
    { a := 0, k:=0, nonnegative := fun _=>le_rfl, usable :=fun _=>le_rfl, supplies := fun _ _ _ => (norm_zero : ‖(0:ℂ)‖=0).le,
      paid := fun i h => (lt_irrefl _ h).elim, kernels:=fun k k' hk => ?_ }
  · have hp i : X.funded (fun _=>w) 0 i 1 := by
      constructor
      all_goals intro i; simp [Stubs.crown,Stubs.cord,X,loaf,SumBudget]
    exact ⟨X,hp _,Or.inl (hp _)⟩
  have ht := WardBin.zeroPrice P.p (R.support k) (R.origins k') (G:=G)
  exact ⟨0,fun _=>le_rfl,by simp,fun u he ha x hX => ht.2.2 _ hX _ he ha⟩
end constants
section circle
variable {C : Family G} {s : Extra.Multi.Scope} {t : Extra.Multi.Tariff} {H : RG.History G} {N p m d i : ℕ} {q : Site (C.side m p)}

lemma huge {z : ℝ} (h0 : 1 ≤ z) (i : ℕ) : width C z 0 i ≤ z⁻¹ := by
  unfold width; rw [pow_zero,one_div]; apply inv_anti₀ (zero_lt_one.trans_le h0)
  unfold Mix.envelope
  have ht : 1 ≤ (C.path.levels.params i).columns := (C.path.levels.params i).columns_ge
  exact (le_mul_of_one_le_right (zero_le_one.trans h0) ht).trans
    (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans h0) (zero_le_one.trans ht)) (Finset.one_le_prod fun i hi=> (C.path.levels.params _).columns_ge))

lemma a_le (S : Schedule) (i : ℕ) : S.a i ≤ 1 := by
  unfold Schedule.a; exact inv_le_one_of_one_le₀ (by exact_mod_cast (S.denominator i).property)

variable (C)

def spotted (N p m : ℕ) (h : m ≤ N) (c : ℂ) (b : Site (C.side m p)) : ℂ := if (Cells.center C.S p h 0).hand b then star c else c
lemma spot_size (h : m ≤ N) (c : ℂ) (b : Site (C.side m p)) : ‖spotted C N p m h c b‖ = ‖c‖ := by unfold spotted; split <;> simp

def issue (d m N p : ℕ) (h : m ≤ N) (c : ℂ) : Lane C.path (census (Site (C.side m p))) N p where
  sites j := upright 0 (camp C p m j) fun k => (C.S.a j:ℂ)^d * spotted C N p m h c k
  load _ := d
  uses v _ := spotted C N p m h c v
abbrev bag (c : ℂ) (h : m≤N) (q : (census (Site (C.side m p))).Mode) := ∏ v ∈ q.val,spotted C N p m h c v
abbrev scale (d i k : ℕ) := ((C.S.a i:ℂ)^d)^k
lemma obtainSignal (H : C.Makes) (h : m≤N) (c : ℂ) (i : (census (Site (C.side m p))).Mode) (j : ℕ) (hj : j ≤ N) (U) :
    (issue C d m N p h c).signal j i U = scale C d j i.val.card * bag C c h i * Extra.Histories.liftVac C.path N p j U := by
  rw [Lane.signal,issue, additions _ _ _ _ (H.wilson.represents N p j hj).good.labels]; unfold scale bag
  rw [Finset.prod_mul_distrib,Finset.prod_const]; dsimp only [Extra.Histories.liftVac]; ring
lemma transfer (H : C.Makes) (h : m≤N) (c : ℂ) (i : (census (Site (C.side m p))).Mode) (j : ℕ) (hj : j < N) :
    let L := issue C d m N p h c
    L.signal j i=(Ride.bump (↑(C.path.S.block j).val) i L.load) •
      (C.path.levels.clock.op j p).push (C.path.β N p (j+1)) (L.signal (j+1) i) := by
  intro L
  rw [show L.signal (j+1) i=_ from
    (show L.signal (j+1) i= (_ : ℂ) • Extra.Histories.liftVac C.path N p (j+1) from funext fun U => obtainSignal C H h c i (j+1) hj U),StepData.push_smul _ _ _ _ (Extra.Histories.vac_integrable _ _ _ _ H.wilson hj), ← Extra.Histories.vac_transfer C.path N p j H.wilson hj]
  funext U; rw [show L=issue .. from rfl, obtainSignal C H h c i j hj.le]; simp only [Ride.bump, issue,Pi.smul_apply,smul_eq_mul,Finset.prod_const]
  rw [←mul_assoc _ _ (Extra.Histories.liftVac _ _ _ _ _), ← mul_assoc, scale, scale,C.S.a_step, Complex.ofReal_div, ←mul_pow, ←mul_pow]
  rw [show C.path.S=C.S from rfl,Complex.ofReal_natCast,mul_div_cancel₀ _ (by exact_mod_cast (C.S.block j).property.ne')]

lemma story {u : ℝ} (H : C.Makes) (m i N p : ℕ) (hm : m ≤ i) (hi : i ≤ N) (h : m ≤ N := hm.trans hi)
    (ht : ticket C 1 N p m i h) (hr : C.ref d ≤ N) (hP : ∀ j, i ≤ j → j ≤ N → 8 ≤ C.path.levels.clock.coverSize j)
    (v : C.label d) (c : ℂ) (hv : v=c • C.refUnit d) (hu : ‖c‖≤u) (hV : 1≤u) :
    Story (m:=m) (i:=i) C (issue C d m N p h c) v (fun r i=>width C r 0 i) u := by
  let V := Site (C.side m p)
  let α := spotted C N p m h c
  have hf j (hj : j≤N) : (C.path.rep N p j).p = C.path.levels.budget j := (H.wilson.represents N p j hj).vac
  refine ⟨hm,hi,fun b=> ⟨rfl,?_⟩,fun j _ _ _=>rfl,fun j h1 h2=>?_,?_, fun j U=> ?_, ?_⟩
  · unfold Tiling.copy; funext U; rw [hv]; change α b= _
    have he := (C.linearO N p d 0).map_smul c (C.refUnit d)
    rw [he,C.constant H _ hr]; dsimp only [α,spotted]; split <;> simp
  · unfold issue; apply incidental
    · intro l
      have hh : ‖(↑(C.S.a j):ℂ)^d* α l‖ ≤ u := by
        rw [norm_mul,norm_pow,Complex.norm_real, Real.norm_of_nonneg (C.S.a_pos _).le,spot_size]
        exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (C.S.a_pos _).le (a_le C.S j))) hu
      exact ((mul_le_mul_of_nonneg_right (huge hV j) (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left hh (by have hi := zero_lt_one.trans_le hV; positivity))).trans (by rw [inv_mul_cancel₀ (zero_lt_one.trans_le hV).ne'])
    · intro a b hT; rw [hf j h2]
      refine ⟨hP _ h1 h2,?_⟩; change (C.path.levels.clock.coverSize j) * _ ≤ _
      have hz := ht.2.2 j h1 h2 a b hT
      rw [mul_one, sq (↑(C.path.levels.clock.coverSize j) : ℝ)] at hz; exact_mod_cast hz
  · intro j; apply continuous_integrable; unfold Ride.Product; exact continuous_finsetProd _ fun i _=>continuous_const
  · rw [obtainSignal C H h c j _ le_rfl, Ride.bump, Ride.Product]; dsimp only [issue]; rw [Finset.prod_const]
    unfold Extra.Histories.liftVac scale; rw [(H.wilson.starts N p).2]; unfold bag; change _= ((C.S.a N : ℂ)^d)^_*_ * _; ring
  intro j t h1 h2 -- t mode not fee; shadow
  exact transfer C H h c t j h2 -- syntax

lemma sphere (H : C.Makes) (hG : G.Simple) {s : Extra.Multi.Scope} {t : Extra.Multi.Tariff} (he : Extra.Multi.Prepared s t C.localSection C.path.levels)
    (d : ℕ) (hd : d<4) (u : ℝ) (_hu : 0<u) : Circle C d u := by
  have ha : 0 < ‖C.refUnit d‖ := by
    apply norm_pos_iff.mpr
    have hv : ((C.S.a (C.ref d):ℂ)^d)≠0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos (C.ref d)).ne')
    apply smul_ne_zero hv
    intro h; have hh := congr_fun h 0
    simp [Frame.e0] at hh
  let a := max (u / ‖C.refUnit d‖) 1
  have ht : 1≤a := le_max_right ..
  refine ⟨a,1,0,zero_lt_one.trans_le ht,le_rfl,fun m i hR hk=> ?_⟩
  filter_upwards [eventually_ge_atTop i] with j h₁
  have hv := hk.1
  have hz : m ≤ j := hv.trans h₁
  refine ⟨hz,fun p h v hp=>?_⟩
  obtain ⟨c,hc⟩ := Push.FiniteDetection.ref_low hG hd v
  rw [hc,norm_smul] at hp
  exact ⟨_,story C H m i j p hv h₁ hz h (hR.trans hz) (fun i _ _=> (he.here i).large) v c hc ((le_div_iff₀ ha).mpr hp |>.trans (le_max_left ..)) ht⟩
end circle

section prices
open Finset Extra.Multi
open Extra.Multi renaming rate → ratesR
variable {C : Family G} {s : Extra.Multi.Scope} {t : Extra.Multi.Tariff} {d i N m p j : ℕ}
def Luxury (C : Family G) (t : Tariff) := ∀ d ≥ 4,∀ (r : ℝ),0<r → ∃ b : ℝ,1≤b ∧ ∀ m i,
    C.ref d ≤ m → Tabs.opens C.path.levels b m i →
    ∀ᶠ N in atTop, ∃ h : m ≤ N, ∀ p, Mix.ticket C b N p m i h → ∀ v : C.label d, ‖v‖ ≤ r →
      ∃ L : Lane C.path (census (Site (C.side m p))) N p,
        Unbilled C L (fun _ => d) (allCopies C p h v) i t ∧
        ∀ j, i ≤ j → j ≤ N → ∀ k,(L.sites j).origins k=Mix.camp C p m j k





end prices
end YM.Further.PhysicalPeriodLimitF933.Toy
