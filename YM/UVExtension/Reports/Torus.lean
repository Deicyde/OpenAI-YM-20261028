import YM.UVExtension.Reports.Periodic
/-!
 # All smooth periodic separated tests, also across seams

 Lifts to continuum cover, integrals over Fund. True Riemann pairing
 for the full periodic arrays and for stride differences at their actual
 mesh. For tiles (using periodic probes in NoHit with compact support
 modulo the period), even continuity suffices in the theorem. The result
 also allows arbitrary continuous nonperiodic functions on the cover
 with the support property here if `orbitSample` using this particular
 closed-right representative convention is wanted. See Poppy/Beach.Shoal
 for the basic (Extraction-compatible) support condition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Beach
open Function Filter Set Metric Lattice RG Wilson Extraction Fallow Poppy
open Tide Swell Lamppost Spire Pier Rafter BoundedContinuousFunction MeasureTheory
open scoped Topology BigOperators Classical ContDiff
variable {a : ℝ}
local notation "Z"=> ball (0:ℂ) a
variable {n m : ℕ}(S:Schedule)(p:ℕ)(F:ℕ→ℂ→ Tabletop n→ℂ) (t:Points n→ℂ)

private lemma fund_compact : IsCompact (closure (Fund S p n)) := by
  let X(r:Var S n 0 p) := Extraction.tag (S.a 0) (fun i=> lift (r i))
  let V := ⋃ r : Var S n 0 p, Metric.closedBall (X r) (4*n*S.a 0)
  have he : IsCompact V := isCompact_iUnion (fun r=> isCompact_closedBall _ _)
  apply he.of_isClosed_subset isClosed_closure
  refine closure_minimal (fun x hx=>mem_iUnion.mpr ⟨bucket (S:=S) 0 p x,?_⟩) he.isClosed
  rw [mem_closedBall,dist_comm]
  exact (le_of_eq (show dist (X (bucket (S:=S) 0 p x)) x=dist (tag (S.a 0) (address (S.a 0) x)) x from by unfold X; rw [← show Extraction.address (S.a 0) x=(fun i=> lift (bucket (S:=S) 0 p x i)) from found hx])).trans (approximate (S.a_pos _) _)

private def testPoint (l:List (Stride n))(N:ℕ)(z:ℂ)(r:Var S n N p) :=
    t (tag (S.a N) (fun i=> lift (r i))) * Poppy.strides (S.a N) (F N z) l (fun i=>lift (r i))

def orbitSample (l:List (Stride n))(N:ℕ)(z:ℂ):ℂ :=
    (S.a N:ℂ)^(4*n)*∑ r:Var S n N p, testPoint S p F t l N z r

def cellLimit (t:Points n→ℂ)(f:ℂ→Points n→ℂ) (z:ℂ):= ∫ x:Points n in Fund S p n,t x*f z x

private lemma tile_sample (l:List (Stride n))(N:ℕ)(z:ℂ)(x:Points n)(hx:x∈Fund S p n):
    let y:= tag (S.a N) (address (S.a N) x)
    stair S (testPoint S p F t l N z) x = t y*tideL S F l N z y := by
  intro y
  rw [stair,indicator_of_mem hx]; unfold testPoint
  rw [← show Extraction.address (S.a N) x = _ from (found (S:=S) (N:=N) hx : address _ x=_)]
  rw [tideL, Poppy.anchored (S.a_pos N) _ _]

private lemma tile_mem (N:ℕ)(x:Points n)(hx:x∈Fund S p n):
    Extraction.tag (S.a N) (address (S.a N) x) ∈ Fund S p n:= by
  rw [(show address (S.a N) x= _ from (found (N:=N) hx : address _ x = _))]
  exact fun i a=> S.places_period (bucket (S:=S) N p x i) a

lemma analyticSample (l:List (Stride n))(N:ℕ)(hp:∀ x:Tabletop n,AnalyticOnNhd ℂ (fun z=> F N z x) Z) :
    AnalyticOnNhd ℂ (orbitSample S p F t l N) Z:= by
  have hx (u:List (Stride n))(x:Tabletop n) : DifferentiableOn ℂ (fun z=> strides (S.a N) (F N z) u x) Z:=by
      induction u generalizing x with
      | nil=> exact hp x|>.differentiableOn
      | cons a u ih => exact ((ih _).sub (ih _)).const_mul _
  exact ((DifferentiableOn.fun_sum fun r (_:r∈Finset.univ)=>
      (hx l (fun i=> lift ((r:Var S n N p) i))).const_mul (_:ℂ)).const_mul (_:ℂ)).analyticOnNhd isOpen_ball

variable {P:ℂ→ Points n→ℂ} (l:List (Stride n))
variable (h : Terrace S m F a (NoHit S p n) P) (hl:l.length ≤ m)
    (ht: Continuous t) (hX: tsupport t ∩ closure (Fund S p n) ⊆ NoHit S p n)
    (hQ : ∀ᶠ i in atTop,∀ x:Tabletop n,AnalyticOnNhd ℂ (fun z=> F i z x) (Metric.ball (0:ℂ) a))
include h hl ht hX hQ
private lemma subdisk (b:ℝ)(hb:0<b)(hc:b<a) : let f z:=ivy (P z) (l.map Stride.axis)
    let X:=Metric.ball (0:ℂ) b
    AnalyticOnNhd ℂ (cellLimit S p t f) X ∧
       (∀ z∈ X, IntegrableOn (fun x=> t x*f z x) (Fund S p n))∧
       TendstoLocallyUniformlyOn (orbitSample S p F t l) (cellLimit S p t f) atTop X := by
  intro f X; let D:= closure (Fund S p n)
  let K := tsupport t ∩ D; let K' := closedBall (0:ℂ) b
  let C:= Fund S p n; have hZ: X⊆K':= ball_subset_closedBall
  have he: K'⊆ Z:= closedBall_subset_ball hc
  let L := tideL S F l; let R i z:= stair S (testPoint S p F t l i z)
  have hY : MeasurableSet C:= (full_box _ _ _).1
  have hK : IsCompact K:= (fund_compact S p).of_isClosed_subset ((isClosed_tsupport (f:=t)).inter isClosed_closure) inter_subset_right
  obtain ⟨g,hg,⟨d,hD⟩,hG⟩:= (h.wand l hl).debt _ hX hK
  have hB : 0≤d:= (norm_nonneg _).trans (hD 0 (he (mem_closedBall_self hb.le)))
  have hp : ∀ᶠ i in atTop,∀ z∈ X,∀ x∈K, ‖L i z x‖ ≤ d+1:=by
    filter_upwards [(h.wand l hl).converges K' (isCompact_closedBall _ _) he K hK hX 0 1 zero_lt_one] with i hi z hz x hx
    have hm: ‖L i z x - f z x‖ ≤ 1:= (hi _ (hZ hz) _ hx).le
    have hv: ‖f z x‖ ≤ d:=by
       let v:K:= ⟨x,hx⟩
       rw [show f z x=g z v from hG v (he (hZ hz))]
       exact ((g z).norm_coe_le_norm v).trans (hD z (he (hZ hz)))
    linarith only [hv,hm,norm_le_norm_sub_add (L i z x) (f z x)]
  obtain ⟨E,hE⟩:= (((fund_compact (n:=n) S p).image ht.norm).bddAbove)
  let W := max 1 E; have hw : 0≤W:= zero_le_one.trans (le_max_left ..)
  let B := C.indicator fun _=> W*(d+1)
  have hI : Integrable B := (integrable_indicator_iff hY).mpr (integrableOn_const (full_box _ _ _).2.ne)
  have hφ : ∀ᶠ i in atTop,∀ z∈ X,∀ x, ‖R i z x‖ ≤ B x :=by
    filter_upwards [hp] with i hi z hz x
    by_cases hx:x∈C
    · unfold R B; let y:= Extraction.tag (S.a i) (address (S.a i) x)
      have hy:y∈D:= subset_closure (tile_mem S p _ _ hx)
      rw [show stair _ _ _= t y* L i z y from tile_sample S p F t l i z x hx,norm_mul,indicator_of_mem hx]
      by_cases hY:y∈ tsupport t
      · exact mul_le_mul ((hE ⟨y,hy,rfl⟩).trans (le_max_right ..)) (hi z hz y ⟨hY,hy⟩) (norm_nonneg _) hw
      rw [image_eq_zero_of_notMem_tsupport hY,norm_zero,zero_mul]
      exact mul_nonneg hw (add_nonneg hB zero_le_one)
    unfold R B stair; rw [indicator_of_notMem hx,indicator_of_notMem hx,norm_zero]
  let G z:= C.indicator (fun x=>t x*f z x)
  have hL(z)(hz:z∈ X) (x:Points n): Tendsto (fun i=> R i z x) atTop (𝓝 (G z x)):=by
    by_cases hx:x∈C; swap
    · unfold R G stair; unfold C at *; simp_rw [indicator_of_notMem hx]; exact tendsto_const_nhds (x:=(0:ℂ))
    let y i:= tag (S.a i) (address (S.a i) x)
    have hy: Tendsto y atTop (𝓝 x):= chosen x
    have hR i: R i z x= t (y i)* L i z (y i):= tile_sample S p F t l i z x hx
    simp_rw [hR,G,indicator_of_mem hx]
    by_cases hY:x∈ tsupport t
    · have hm: x∈ NoHit S p n:= hX ⟨hY,subset_closure hx⟩
      obtain ⟨K0,hK0,hp,hV⟩:= exists_compact_subset (Fallow.no_wrap S p n) hm
      obtain ⟨g,hg,hH,he'⟩:= (h.wand l hl).debt _ hV hK0
      have hT: ContinuousOn (f z) K0 := (continuousOn_iff_continuous_restrict).2 (by
        rw [show K0.restrict (f z)= g z from funext fun i=>he' i (he (hZ hz))]; exact (g z).continuous)
      refine (ht.continuousAt.tendsto.comp hy).mul ?_
      have hw:= ((hT x (interior_subset hp)).continuousAt (mem_interior_iff_mem_nhds.mp hp)).tendsto.comp hy
      have hφ: Tendsto (fun i=> L i z (y i)-f z (y i)) atTop (𝓝 0) := by
        refine Metric.tendsto_nhds.mpr fun ε hε=>?_
        filter_upwards [(h.wand l hl).converges K' (isCompact_closedBall _ _) he K0 hK0 hV 0 ε hε,
            hy.eventually (mem_interior_iff_mem_nhds.mp hp)] with i hi hj
        rw [dist_zero_right]
        exact hi z (hZ hz) _ hj
      simpa only [Function.comp_apply,sub_add_cancel,zero_add] using! hφ.add hw
    have hx := image_eq_zero_of_notMem_tsupport hY; rw [hx,zero_mul]
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x:=(0:ℂ)))
    filter_upwards [hy.eventually ((isClosed_tsupport (f:=t)).isOpen_compl.mem_nhds hY)] with i hi
    exact (mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport hi) _).symm
  have hk(i:ℕ)(z): Integrable (R i z):= stair_int _
  have hc'(z)(hz:z∈X): Integrable (G z):=by
    have hh':∀ᵐ x:Points n, Tendsto (fun i=> R i z x) atTop (𝓝 (G z x)):= Eventually.of_forall (hL z hz)
    exact hI.mono' (aestronglyMeasurable_of_tendsto_ae atTop (fun n=> (hk n z).aestronglyMeasurable) hh') (hh'.mono fun x hx=> le_of_tendsto hx.norm (hφ.mono fun i hi=> hi z hz x))
  have hv(z)(hz:z∈X): Tendsto (fun i=> orbitSample S p F t l i z) atTop (𝓝 (cellLimit S p t f z)):=by
    have hk:= tendsto_integral_filter_of_dominated_convergence B (Eventually.of_forall (fun n=>(hk n z).aestronglyMeasurable)) (hφ.mono fun i hi=> Eventually.of_forall (hi z hz)) hI (Eventually.of_forall (hL z hz))
    unfold cellLimit; rw [← integral_indicator hY (f:=fun x=>t x*f z x)]; exact hk.congr' (Eventually.of_forall fun i=> stair_integral _)
  obtain ⟨N,hN⟩:=eventually_atTop.mp (hφ.and hQ)
  let V i:= if i≥ N then orbitSample S p F t l i else (fun _=>0)
  let M:=max 1 (∫ x,B x)
  have H: V =ᶠ[atTop] orbitSample S p F t l:= (eventually_ge_atTop N).mono fun i hi=> if_pos hi
  have he' (i): DifferentiableOn ℂ (V i) X ∧ ∀ z∈ X, ‖V i z‖≤ M:=by
    unfold V; split
    next hi=> refine ⟨((analyticSample S p F t l i (hN i hi).2).differentiableOn.mono (hZ.trans he)),fun z hz=>?_⟩
              unfold orbitSample
              rw [← stair_integral (testPoint S p F t l i z)]
              exact (norm_integral_le_integral_norm _).trans ((integral_mono (hk i z|>.norm) hI ((hN i hi).1 _ hz)).trans (le_max_right ..))
    next H=> exact ⟨differentiableOn_const _,fun _ _=> norm_zero.trans_le (zero_le_one.trans (le_max_left ..))⟩
  have hv' (x:ℝ)(hx:|x|<b): Arrives (fun n=> V n x):=by
    let z:Row b:= ⟨x,hx⟩
    exact ⟨_, (hv _ ((desk b hb).within z)).congr' (H.mono (fun i hi=> congr_fun hi.symm (x:ℂ)))⟩
  obtain ⟨g',hg',hr⟩:= Camp.viva b hb M (F:=V) he' hv'
  have ht: TendstoLocallyUniformlyOn V g' atTop X:=by simpa only [iteratedDeriv_zero] using! hr 0
  have hE : EqOn g' (cellLimit S p t f) X:= fun z hz=> tendsto_nhds_unique ((ht.tendsto_at hz).congr' (H.mono fun i hi=> congr_fun hi z)) (hv _ hz)
  refine ⟨(hg'.differentiableOn.congr hE.symm).analyticOnNhd isOpen_ball,fun z hz=>(integrable_indicator_iff hY).mp (hc' _ hz),((ht.congr_inseparable ?_).congr_right hE)⟩
  exact H.mono fun i hi z hz=> by rw [show V i=_ from hi]

lemma periodic_tests (j:ℕ) : let f z:=ivy (P z) (l.map Stride.axis)
    AnalyticOnNhd ℂ (cellLimit S p t f) Z ∧
        (∀ z∈ Z, IntegrableOn (fun x=> t x*f z x) (Fund S p n)) ∧
        TendstoLocallyUniformlyOn (fun i=>iteratedDeriv j (orbitSample S p F t l i))
           (iteratedDeriv j (cellLimit S p t f)) atTop Z := by
  intro f
  have H(b)(hb:0<b)(hc:b<a):= subdisk S p F t l h hl ht hX hQ b hb hc
  have he z (hz:z∈ Z) : ∃ b, 0 < b∧ b < a ∧ z∈ ball (0:ℂ) b := by
    obtain ⟨b,hb,hh⟩:= exists_between (mem_ball_zero_iff.mp hz)
    exact ⟨b,(norm_nonneg z).trans_lt hb,hh,mem_ball_zero_iff.mpr hb⟩
  have hp : TendstoLocallyUniformlyOn (orbitSample S p F t l) (cellLimit S p t f) atTop Z := by
     refine IsOpen.tendstoLocallyUniformlyOn_iff_forall_tendsto isOpen_ball|>.2 (fun z hz=>?_)
     obtain ⟨b,hb,hB,hx⟩:=he z hz
     exact IsOpen.tendstoLocallyUniformlyOn_iff_forall_tendsto isOpen_ball|>.1 (H b hb hB|>.2.2) z hx
  refine ⟨fun z hz=>?_,fun z hz=>?_,?_⟩
  · obtain ⟨b,hb,hB,hx⟩:=he z hz; exact (H b hb hB).1 z hx
  · obtain ⟨b,hb,hB,hx⟩:=he z hz; exact (H b hb hB).2.1 z hx
  induction j with
  | zero=> simpa only [iteratedDeriv_zero] using hp
  | succ j ih=>
    simp_rw [iteratedDeriv_succ]
    apply ih.deriv _ isOpen_ball
    filter_upwards [hQ] with i hi z hz
    rw [iteratedDeriv_eq_iterate]
    exact (((analyticSample S p F t l i hi) z hz).iterated_deriv j).differentiableAt.differentiableWithinAt
end YM.UVExtension.Beach
#print axioms YM.UVExtension.Beach.periodic_tests
