import YM.Bid.Station
import YM.Next.EXTRACTION.Tails
import YM.Work.A01.Conserve
import YM.Work.A15
import YM.Work.C13.Decay
import YM.Work.G07.Calculus

/-!
Cutoff shell independence, translation to arbitrary center, and continuity
on configurations with admissible window. Minus gradient = outward flux
when enclosing the marked field. No deletion or replacement of any other
fields for independence; the *difference* vanishes on neighborhoods of all
of them including the center. No assertion about contact distributions in this
continuum identity. cf. ; consumes quotient conservation à la A01.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Annular
open Table Work.A01 Analysis Function Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {L : Register G} {S : Table L} {W : DiffPlan S} {n d : ℕ}
  {χ ψ : E4 → ℝ} {x : Points (n+1)} {H : S.RealSpin}

def about (J : S.Stress) (χ : E4 → ℝ) (V : E4 → E4) (x : Points (n+1)) := @flux _ _ S d n J χ (fun y => V (y-x 0)) x

lemma expanded {J : S.Stress} {V : E4 → E4} (hx : x∈conf _) (hw : Window x χ) (h : S.Smooth) (q : Fin n → S.Tag) (B : S.Field d)
    (hv : ∀ b : Axis, Continuous fun y => V y b) (a : Axis) :
    Integrable (fun y => D (basis a) χ y • current J V x (Fin.cons ⟨d,B⟩ q) a y) ∧
    ∑ b : Axis, ∫ y, term J χ V x q B a b y = ∫ y, D (basis a) χ y • current J V x (Fin.cons ⟨d,B⟩ q) a y := by
  have he (y) : D (basis a) χ y • current J V x (Fin.cons ⟨d,B⟩ q) a y = ∑ b, term J χ V x q B a b y := by
    simp only [term,current,Complex.ofReal_mul,Complex.real_smul,Finset.mul_sum,mul_assoc]
  simp_rw [he]
  have ht b := term_integrable J χ V x q B h hx hw a b (hv b)
  exact ⟨integrable_finsetSum _ fun i _ => ht i,(integral_finsetSum _ fun i _ => ht i).symm⟩

lemma difference_window (hx : x∈conf _) (hw : Window x χ) (ht : Window x ψ) : ∀ y∈tsupport (χ-ψ), Points.cons y x ∈ conf _ := by
  refine fun y hy => conf_cons hx (fun i => Fin.cases (fun hz => ?_) (fun j hz => ?_) i)
  · subst y
    exact (notMem_tsupport_iff_eventuallyEq.mpr (by
      filter_upwards [hw.2.2.1,ht.2.2.1] with y h h'; simp [h,h'])) hy
  · subst y
    exact (notMem_tsupport_iff_eventuallyEq.mpr (by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (hw.2.2.2 j),notMem_tsupport_iff_eventuallyEq.mp (ht.2.2.2 j)] with y h h'
      simp [h,h'])) hy

lemma independent (hs : S.Smooth) (hd : W.Derivatives S) {J : S.Stress} (hJ : Conserved W H J)
    (V : E4 → E4) (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b)) (hk : killing V)
    (hx : x∈conf _) (hw : Window x χ) (ht : Window x ψ) (q : Fin n → S.Tag) (B : S.Field d) :
    flux J χ V x q B = flux J ψ V x q B := by
  have he := cutoff_zero hs W hd J hJ V hv hk x (Fin.cons ⟨d,B⟩ q) (χ-ψ) (hw.1.sub ht.1) (hw.2.1.sub ht.2.1) (difference_window hx hw ht)
  let F := current J V x (Fin.cons (α:= fun _ => S.Tag) ⟨d,B⟩ q)
  change -(∑ a, ∫ y, D (basis a) (χ-ψ) y • F a y)=0 at he
  have hc (y : E4) (a : Axis) : D (basis a) (χ-ψ) y • F a y = D (basis a) χ y • F a y - D (basis a) ψ y • F a y := by
    simp only [D,fderiv_sub ((hw.1.differentiable (by simp)) y) ((ht.1.differentiable (by simp)) y),_root_.sub_apply,sub_smul]
  have hp a := expanded (J:=J) hx hw hs q B (fun b => (hv b).continuous) a
  have hr a := expanded (J:=J) hx ht hs q B (fun b => (hv b).continuous) a
  simp_rw [hc] at he
  have hu a : (∫ y, (D (basis a) χ y • F a y - D (basis a) ψ y • F a y)) = (∑ b, ∫ y, term J χ V x q B a b y) - ∑ b, ∫ y, term J ψ V x q B a b y := by
    rw [integral_sub (hp a).1 (hr a).1, (hp a).2,(hr a).2]
  simp_rw [hu] at he
  rw [Finset.sum_sub_distrib, neg_eq_zero, sub_eq_zero] at he
  exact congr_arg Neg.neg he

lemma independent_about (hs : S.Smooth) (hd : W.Derivatives S) {J : S.Stress} (hJ : Conserved W H J)
    (V : E4 → E4) (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b)) (hk : killing V)
    (hx : x∈conf _) (hw : Window x χ) (ht : Window x ψ) (q : Fin n → S.Tag) (B : S.Field d) :
    about J χ V x q B = about J ψ V x q B := by
  refine independent hs hd hJ _ (fun b => (hv b).comp (contDiff_id.sub contDiff_const)) (fun a b y => ?_) hx hw ht q B
  change D (basis a) (fun z => V (z-x 0) b) y = - D (basis b) (fun z => V (z-x 0) a) y
  simpa only [D,sub_eq_add_neg,fderiv_comp_add_right (f:=fun z => V z b) (-x 0), fderiv_comp_add_right (f:=fun z => V z a) (-x 0)] using hk a b (y-x 0)

lemma shifted_window (c : E4) (hw : Window x χ) : Window (Points.across c x) (fun y => χ (y-c)) := by
  let l (y : E4) := y-c
  have hc (i : Fin (n+1)) : Tendsto l (𝓝 (Points.across c x i)) (𝓝 (x i)) := add_sub_cancel_right (x i) c ▸ (continuous_id.sub continuous_const : Continuous l).continuousAt
  refine ⟨hw.1.comp (contDiff_id.sub contDiff_const), ?_, hw.2.2.1.comp_tendsto (hc 0),fun i => notMem_tsupport_iff_eventuallyEq.mpr ((notMem_tsupport_iff_eventuallyEq.mp (hw.2.2.2 i)).comp_tendsto (hc i.succ))⟩
  simp only [sub_eq_add_neg]
  exact hw.2.1.comp_homeomorph (Homeomorph.addRight (-c))

lemma homogeneous (ht : S.Homogeneous) {u : Points n} (hu : u∈conf _) (q : Fin n → S.Tag) (c : E4) :
    S.useAt S (Points.across c u) q = S.useAt S u q := ht n u hu c (fun i => ⟨_,S.representative (q i).1 (q i).2⟩)

lemma across_cons (x : Points n) (y c : E4) : Points.cons (y+c) (Points.across c x) = Points.across c (Points.cons y x) := by
  ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Points.cons]

lemma moved (J : S.Stress) (V : E4 → E4) (c : E4) (ht : S.Homogeneous) (hx : x∈conf _) (hw : Window x χ) (q : Fin n → S.Tag) (B : S.Field d) :
    about J (fun y => χ (y-c)) V (Points.across c x) q B = about J χ V x q B := by
  have he a b y : term J (fun y => χ (y-c)) (fun y => V (y-Points.across c x 0)) (Points.across c x) q B a b (y+c) =
      term J χ (fun y => V (y-x 0)) x q B a b y := by
    have hc : D (basis a) (fun y => χ (y-c)) (y+c) = D (basis a) χ y := by rw [D,show (fun y => χ (y-c)) = (fun y => χ (y + -c)) by simp only [sub_eq_add_neg], fderiv_comp_add_right (-c),← sub_eq_add_neg,add_sub_cancel_right,D]
    unfold term
    simp only [hc,Points.across_coord, add_sub_add_right_eq_sub, across_cons]
    by_cases hz : D (basis a) χ y = 0
    · simp [hz]
    rw [homogeneous ht (separated_of_D hx hw hz)]
  have hi a b := integral_add_right_eq_self (term J (fun y => χ (y-c)) (fun y => V (y-Points.across c x 0)) (Points.across c x) q B a b) c (μ:=volume)
  simp_rw [he] at hi
  simp only [about,flux,hi]

@[fun_prop] lemma cons_continuous : Continuous (fun p : Points n × E4 => Points.cons p.2 p.1) := by
  apply PiLp.continuous_toLp 2 _ |>.comp
    (f:= fun p : Points n × E4 => Fin.cons (α:=fun _ => E4) p.2 p.1.ofLp)
  apply continuous_pi
  intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp <;> fun_prop

lemma window_open (hw : Window x χ) : ∀ᶠ t in 𝓝 x, Window t χ := by
  have he (i : Fin n) := (show Continuous (fun x : Points (n+1) => x i.succ) by fun_prop).continuousAt (x := x) |>.eventually
      ((isClosed_tsupport χ).isOpen_compl.mem_nhds (show x i.succ∈(tsupport χ)ᶜ from hw.2.2.2 i))
  have ht := (show Continuous (fun x : Points (n+1) => x 0) by fun_prop).continuousAt (x := x) |>.eventually (eventually_eventually_nhds.mpr hw.2.2.1)
  filter_upwards [eventually_all.mpr he,ht] with t hy hz
  exact ⟨hw.1,hw.2.1,hz,hy⟩

lemma term_joint (J : S.Stress) (V : E4 → E4) (hv : ∀ b : Axis, Continuous (fun y => V y b)) (hs : S.Smooth) (hx : x∈conf _) (hw : Window x χ)
    (q : Fin n → S.Tag) (B : S.Field d) (a b : Axis) (y : E4) :
    ContinuousAt (fun p : Points (n+1) × E4 => term J χ (fun y => V (y-p.1 0)) p.1 q B a b p.2) (x,y) := by
  by_cases hy : y ∈ tsupport (fderiv ℝ χ)
  · have hu := S.class_smooth S hs (Fin.cons ⟨4,J a b⟩ (Fin.cons (α:=fun _ => S.Tag) ⟨d,B⟩ q)) |>.continuousOn
    have hp := hu.continuousAt ((conf_open _).mem_nhds (window_separated hx hw hy)) |>.comp (f:= fun p : Points (n+1) × E4 => Points.cons p.2 p.1) (cons_continuous.continuousAt (x:=(x,y)))
    have hd : Continuous (D (basis a) χ) := (hw.1.continuous_fderiv (by simp)).clm_apply continuous_const
    unfold term
    refine (Complex.continuous_ofReal.comp ((hd.comp continuous_snd).mul ((hv b).comp ?_))).continuousAt.mul hp
    fun_prop
  have he := continuous_snd.continuousAt (x:=(x,y)) |>.eventually (notMem_tsupport_iff_eventuallyEq.mp hy)
  refine (continuousAt_const (y:=(0:ℂ))).congr (he.mono ?_)
  intro p hp
  change (0 : ℂ) = term _ _ _ _ _ _ _ _ _
  simp [term,D,show fderiv ℝ χ p.2 = 0 from hp]

lemma flux_continuous (J : S.Stress) (V : E4 → E4) (hv : ∀ b : Axis, Continuous (fun y => V y b)) (hs : S.Smooth) (hx : x∈conf _) (hw : Window x χ)
    (q : Fin n → S.Tag) (B : S.Field d) : ContinuousAt (fun x => about J χ V x q B) x := by
  let E := tsupport (fderiv ℝ χ)
  have hE : IsCompact E := hw.2.1.fderiv ℝ
  obtain ⟨K,hK,h,hk⟩ := local_compact_nhds (show {x : Points (n+1) | x∈conf _ ∧ Window x χ} ∈ 𝓝 x from ((conf_open _).eventually_mem hx).and (window_open hw))
  have ht (a b : Axis) : ContinuousAt (fun x => ∫ y, term J χ (fun y => V (y-x 0)) x q B a b y) x := by
    obtain ⟨A,hA⟩ := (hk.prod hE).exists_bound_of_continuousOn (fun (p : Points (n+1) × E4) hp =>
      (term_joint J V hv hs (h hp.1).1 (h hp.1).2 q B a b p.2).continuousWithinAt)
    refine continuousAt_of_dominated (bound:= E.indicator (fun _ => A)) ?_ ?_
      ((integrable_indicator_iff hE.measurableSet).2 (integrableOn_const hE.measure_lt_top.ne)) (.of_forall fun y =>
        (term_joint J V hv hs hx hw q B a b y).comp (f:=fun t => (t,y)) (show Continuous (fun t : Points (n+1) => (t,y)) by fun_prop).continuousAt)
    · filter_upwards [hK] with u hu
      exact ((term_integrable J χ _ u q B hs (h hu).1 (h hu).2 a b ((hv b).comp (continuous_id.sub continuous_const))).aestronglyMeasurable)
    · filter_upwards [hK] with u hu
      refine .of_forall fun y => ?_
      by_cases hy : y∈E
      · rw [indicator_of_mem hy]; exact hA (u,y) ⟨hu,hy⟩
      · simp [indicator_of_notMem hy,term,D,image_eq_zero_of_notMem_tsupport hy]
  exact Tendsto.neg (tendsto_finsetSum _ (fun a _ => tendsto_finsetSum _ fun b _ => ht a b))
end YM.StressFlux.Annular
