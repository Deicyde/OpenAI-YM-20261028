import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Typhos
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a α β γ d η σ W s b μ : ℝ} {j B : ℕ}
open Brush
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
namespace Silica.Clutch
private lemma member {l v : ℕ} (T : Tube G S) (R : Rep G f) (i : LogLetter c f) : Raw.space T 0 v R i⊆ Raw.space T l v R i := by
  have h {c f} (p : Ratio c f) (Y : Support f):enlargement p 0 v Y ⊆ enlargement p l v Y := Corona.halo_mono (by omega) (Subset.refl _)
  rcases i with i|i|i|i|i|i
  · exact h _ _
  all_goals exact Finset.image_subset_image (h _ _)

private lemma addSales {ι : Type*} {x : ι→ Support c} {s : ι→ℕ} {u v : ι→ℝ} (p : Sales B a W x u s d) (h : Sales B a W x v s η) :
    Sales B a W x (fun i=> u i+v i) s (d+η) := by
  refine ⟨fun j=> add_nonneg (p.nonneg _) (h.nonneg _),fun i=> ?_⟩
  convert! budget_plus (p.hit i) (h.hit i) using 1; ext j; by_cases hv : i∈x j <;> simp [hv, Reserves.tariff,add_mul]
private lemma noneSales {ι : Type*} (X : ι → Support c) (Y : ι → ℕ) : Sales B a W X (fun _=>0) Y 0 := by
  refine ⟨fun _=> le_rfl,fun j=>?_⟩; simp [Reserves.tariff, SumBudget]
private def crownW (c f : Side) (z : Pairs c→ℝ) : LogLetter c f→ℝ :=
    Sum.elim (fun _=>0) (Sum.elim (fun _=>0) (Sum.elim (fun _=>0) (Sum.elim (fun _=>0) (Sum.elim (fun _=>0) z))))
private lemma stamped {l : ℕ} {z : Pairs c→ℝ} (p : Sales B a W (bothFoot (atOne _) l B T.down) z (bothCharge T.down) d) :
    Sales B a W (Raw.space T l B R) (crownW c f z) (Raw.extra T R) d := by
  have hp:= Sales.together (noneSales (regularFoot S.ratio l B R) (regularExtra R))
    (Sales.together (noneSales (atomFoot S.ratio l B R.path.cubic) (atomCharge R.path.cubic))
    (Sales.together (noneSales (atomFoot S.ratio l B R.path.quartic) (atomCharge R.path.quartic))
      (Sales.together (noneSales (atomFoot S.ratio l B R.path.loop) (atomCharge R.path.loop))
      (Sales.together (noneSales (bothFoot S.ratio l B R.path) (bothCharge R.path)) p))))
  rw [zero_add,zero_add,zero_add,zero_add,zero_add] at hp; exact hp

private lemma catalog (z : Pairs c → ℝ) (v : LogLetter c f → ℝ) (u : Config G f) (V : E → Config G c) (hq : 0≤d)
    (h : ∀ i U, |expo T s R u U i| ≤ v i) (hv : ∀ i,0≤ v i)
    (hp : ∀ i,Brush j (z i) (d*bothCharge T.down i) (fun y=>icicle T.down (V y) (till s) S.patch.L.val (-(- orientation*R.beta)) i) x) :
    ∀ i : LogLetter c f, Brush j (v i+crownW c f z i) (d*Raw.extra T R i) (fun y=> nest T s (V y) u R i) x := by
  intro i
  let F (i:LogLetter c f) := expo T s R u (V x) i
  rcases i with i|i|i|i|i|i
  · change Brush _ _ _ (fun _=> -(R.activities.regularOccurrence R.p i u)) _
    exact (Brush.certified (mul_nonneg hq (Nat.cast_nonneg _)) _).climb ((h (.inl i) (1:Config G c)).trans (le_add_of_nonneg_right (le_refl 0))) le_rfl
  · change Brush _ _ _ (fun _=> translateValue ..) _; exact ((Brush.certified (mul_nonneg hq (Nat.cast_nonneg _)) _).climb
       ((h (.inr (.inl i)) (1:Config G c)).trans (le_add_of_nonneg_right (le_refl 0))) le_rfl)
  · change Brush _ _ _ (fun _=>translateValue ..) _; exact ((Brush.certified (mul_nonneg hq (Nat.cast_nonneg _)) _).climb
      ((h (.inr (.inr (.inl i))) (1:Config G c)).trans (le_add_of_nonneg_right (le_refl 0))) le_rfl)
  · change Brush _ _ _ (fun _=>translateValue ..) _; exact ((Brush.certified (mul_nonneg hq (Nat.cast_nonneg _)) _).climb
       ((h (.inr (.inr (.inr (.inl i)))) (1:Config G c)).trans (le_add_of_nonneg_right (le_refl 0))) le_rfl)
  · change Brush _ _ _ (fun _=>pairValue ..) _; exact ((Brush.certified (mul_nonneg hq (Nat.cast_nonneg _)) _).climb
       ((h (.inr (.inr (.inr (.inr (.inl i))))) (1:Config G c)).trans (le_add_of_nonneg_right (le_refl 0))) le_rfl)
  exact (hp i).climb (le_add_of_nonneg_left (hv _)) le_rfl

open PhysicalNext.Repeat.Height
-- Adapted Clutch.hearth on graded prices
lemma hearthGrades (P : Teller G) (l : ℕ) {b η : ℝ} (hη : 0<η) (hx : 4*η < P.top.supportExponent)
    (hy : 8*η<P.top.width) (hz : 8*η<P.below.width) (hA : 0≤ b) : ∃ n:ℕ, ∀ (L:Side), n≤ L.val → ∀ (j:ℕ)
    (χ : Chi) (a r : ℝ), -(1/2:ℝ)<r → ∀ f g, Rate G L (-(1/2)) f → Rate G L (-(1/2)) g →
    ∃ B, Rate G L 0 B ∧ (∀ x,0≤B x) ∧ ∀ᶠ x in atTop, ∀ (c f':Side) (S:StepData c f') (T : Tube G S) (R : Rep G f'),
      S.patch.L=L → Intake P T x R → ∃ (u : LogLetter c f'→ℝ) (w : ℕ → ℝ), let M:=radiusB x; let e:=Raw.space T l M R
      Sales M b η e (fun i=>grow G L x^Raw.extraA c f' i*u i) (Raw.extra T R) (betaF G x L ^ r) ∧ Sales M b η (forcedFoot S.ratio l M R) w (forcedExtra R) (betaF G x L ^ r) ∧
        ∀ (F : Forest S.ratio) (X : Coat T F) (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Config G f')
        (V:E→ Config G c) (Y:E→ Directions G f') (p:E) (W : E→ Air f' G) (t : Air f' G), X.x=x → X.χ=χ → Mode V p j (f x) →
        Clutch X t a R.beta (g x) p j V Y W →
          (∀ i, Brush j (u i) (B x*(coverNumber M (e i)+(Raw.extra T R i:ℝ))) (fun y=> frost (vary X (V y)) a R (Y y) U i) p) ∧
          ∀ i, Brush j (w i) (B x*(coverNumber M (forcedFoot S.ratio l M R i)+(forcedExtra R i:ℝ)))
            (fun y=> sheath (vary X (V y)) a R (Y y) U i) p := by
  obtain ⟨n,hp⟩:= Raw.inherit_multi G P l hη hA hx hy hz
  refine ⟨n,fun L hm j χ a r hr f g h hG=>?_⟩
  obtain ⟨s,h₁,h₂⟩:= exists_between hr
  obtain ⟨p,H,H',hX⟩:= dicers P L (w:=-2) (by norm_num) hA hη hz h j l
  obtain ⟨Q,hQ,hV,hT⟩:= central G L χ j hG (2*a)
  refine ⟨fun x=> p x+Q x,H.add hQ,fun x=> add_nonneg (H' _) (hV _),?_⟩
  let d x:= grow G L x ^ 2* betaF G x L ^ (-2:ℝ)
  have hT':∀ᶠ x in atTop, d x ≤ betaF G x L^ s:= (((Rate.power (G:=G) (L:=L) (a:=3/8)).pow 2).mul (Rate.power (a:=-2)) s (by push_cast; linarith only [h₁])).mono fun x hx=> (le_abs_self _).trans hx
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,hT',hX,hT,hp L hm s h₁ r, ((Rate.power (G:=G) (L:=L) (a:=s)).mul_left 2) r h₂] with x hv he₁ h hp hy hz c f' S T R hs hY
  obtain ⟨z,hZ,hz'⟩:= h _ _ S T R hs hY
  obtain ⟨u,hu,hr,w,hw,hW⟩:= hy _ _ S T R hs hY
  refine ⟨fun i=> u i+crownW c f' z i,w,?_,hW,?_⟩
  · let t := grow G L x
    have hw : 1 ≤ t:= Real.one_le_rpow hv (by norm_num)
    have H:= (boost_price hZ (pow_nonneg (zero_le_one.trans hw) 2)).raise he₁
    have hh : Sales (radiusB x) b η (Raw.space T l (radiusB x) R) (fun p=> grow G L x ^ Raw.extraA c f' p*(u p+crownW c f' z p)) (Raw.extra T R) (betaF G x L^s + betaF G x L^s) := by
      have hz : (fun i:LogLetter c f'=> grow G L x^Raw.extraA c f' i*crownW c f' z i)= crownW c f' (fun p=> t^2*z p) := funext fun p=> by rcases p with p|p|p|p|p|p <;> simp only [Sum.elim,crownW,Raw.extraA,t,mul_zero]
      simp_rw [mul_add,show ∀ i,grow G L x^Raw.extraA c f' i*crownW c f' z i=_ from congr_fun hz]; exact addSales hr (stamped H)
    apply hh.raise
    rw [← two_mul]; exact (le_abs_self _).trans hz
  intro F X E _ _ U V Y y W t hX hx he hh
  have hP := H' X.x; have hG := hV X.x
  have ha:1≤ grow G L x:=Real.one_le_rpow hv (by norm_num)
  subst x; let x:=X.x
  have hk:= catalog (s:=x) z u U V hP (fun i V=>hu U V i) (Raw.store_price _ hr ha).nonneg (fun i=> by have he:=hz' E y V he i; rw [hs]; exact he)
  have hB O O' (he:O⊆O') := hp _ _ S T F X rfl hx hs (show 0 < 2*a*X.t by rw [mul_assoc]; exact mul_pos (by norm_num) hh.pulse) E t a R.beta y V Y W hh O O' he
  have hf (v w:ℕ) : p X.x*w+Q X.x*v ≤ (p X.x+Q X.x)*(v+(w:ℝ)) := by nlinarith [Nat.cast_nonneg (α:=ℝ) v,Nat.cast_nonneg (α:=ℝ) w]
  refine ⟨fun i=>?_,fun i=>?_⟩
  · exact ((hk i).paints (hB (Raw.space T 0 X.B R i) _ (member T R _))).climb (mul_one _).le (hf _ _)
  let s:= forcedFoot S.ratio l X.B R i; let j:= forcedExtra R i
  have hΛ:= hB (forcedFoot S.ratio 0 X.B R i) s (Corona.halo_mono (by omega) (Subset.refl _))
  exact (((Brush.certified (show 0≤p X.x*j from mul_nonneg hP (Nat.cast_nonneg _)) _).climb (hw i U) le_rfl).paints hΛ).climb (mul_one _).le
    (hf _ j)
end Silica.Clutch
end YM.ConnectedActivityE6.Blaze
