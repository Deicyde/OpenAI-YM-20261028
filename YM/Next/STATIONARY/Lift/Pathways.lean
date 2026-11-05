import YM.Next.STATIONARY.Level.SliceGate
import YM.Next.STATIONARY.Lift.ManyLegs
import YM.Work.F08.Width



set_option autoImplicit false
/-! Reality and color projection, *after* cochain lift. -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Bloch Laurent Filter Finset Asymptotics
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
variable {t n : ℕ} {σ A : ℝ}

-- normalization of reality as in spectral Bed.
lemma curl_real (p : Fin n → Momentum) (g : CurRun n → ℂ) (hp : ∀ i, star (p i)=p i) (i : Run n) :
    star (fromCurl (-p) g i) = fromCurl p (fun a => star (g a)) i := by
  have H (n : ℕ) (p : Momentum) (hp : star p=p) a b : star (symbol n (-p) a b)=symbol n p a b := by
    rw [← reading,show -p=-star p by rw [hp], Row.conjugate]
    simp [reading]
  unfold fromCurl
  simp only [star_sum,star_mul,star_prod,Pi.neg_apply,H _ _ (hp _)]
  exact sum_congr rfl fun a _ => mul_comm ..

lemma axes_flip {α : Type} (r : Corn α) : axes (-r)=-(axes r) := by ext1 j; simp [axes]
lemma plotted_flip (p : Space t) : plotted (-p) = -(plotted p) := by
  ext1 j; refine Fin.cases ?_ (fun j => ?_) j
  · simp only [plotted, Pi.neg_apply,Fin.cons_zero,missing]
    congr 1; simp_rw [← Finset.sum_neg_distrib]; rfl
  simp only [plotted, Pi.neg_apply,Fin.cons_succ]; rfl
lemma real_plot (p : Corn (Keys t)) (i) : star (plotted (axes p) i)=plotted (axes p) i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [plotted, Fin.cons_zero, miss_phase,axes_real]
  ext1 j
  simp [axes,plotted,projected]

def readable {α : Type} [Fintype α] (f : Shift α → ℝ) (p : Phase α) := Laurent.read (fun i => (f i:ℂ)) p
lemma re_cast {α : Type} [Fintype α] {u : Phase α → ℂ} (h : Firm σ A u) {p : Phase α} (he : star p=p) :
    readable (fun x => (market u 0 x).re) p = (u p+star (u (-p)))/2 := by
  have hs := h.width_pos
  have hh := h.1.issues h.2 (σ/2) (σ/3) (by positivity) (by positivity) (by linarith)
  rw [readable, Work.F07.readRealPart hh (by linarith) he,h.1.paints h.2 _ (h.in_range he),
    h.1.paints h.2 _ (h.in_range (by rw [star_neg,he]))]

lemma real_rescue (f : Run (t+1) → Space t → ℂ) (hp : ∀ i p, star p=p → star (f i (-p))=f i p)
    (g : CurRun (t+1) → Space t → ℂ) (hg : ∀ i, Firm σ A (g i)) (h : ∀ p : Corn (Keys t), ∀ b,
      fromCurl (plotted (axes p)) (fun i => g i (axes p)) b=f b (axes p)) (p : Corn (Keys t)) (i : Run (t+1)) :
    fromCurl (plotted (axes p)) (fun a => readable (fun x => (market (g a) 0 x).re) (axes p)) i=f i (axes p) := by
  have he := h (-p) i
  rw [axes_flip,plotted_flip] at he
  have hw : star (fromCurl (-plotted (axes p)) (fun i => g i (-axes p)) i)=f i (axes p) :=
      (congr_arg star (by simpa only [axes_flip] using he)).trans (hp i _ (axes_real p))
  rw [curl_real _ _ (real_plot p) i] at hw
  have hx : ∀ (a : CurRun (t+1)), readable (fun x => (market (g a) 0 x).re) (axes p) =
      (g a (axes p)+star (g a (-axes p)))/2 := fun a => re_cast (hg a) (axes_real p)
  unfold fromCurl
  simp_rw [hx,← mul_div_assoc,mul_add,← Finset.sum_div,sum_add_distrib]
  change (fromCurl (plotted (axes p)) (fun i => g i (axes p)) i +
    fromCurl (plotted (axes p)) _ i)/2=_
  rw [h _ _,hw]; ring

abbrev Ink (G : Gauge) (n : ℕ) := Fin n → G.ColorIndex
variable {G : Gauge}

def paints (G : Gauge) (n : ℕ) : Submodule ℝ (Ink G n → ℝ) where
    carrier := {w | ∀ (u : G.El) (a : Fin n → G.Color),
      (∑ x, w x * ∏ i, G.adjoint u (a i) (x i)) = ∑ x, w x * ∏ i, (a i) (x i)}
    zero_mem' := fun _ _ => by simp
    add_mem' := fun {x y} h k u a => by simp only [Pi.add_apply, add_mul,Finset.sum_add_distrib]; rw [h,k]
    smul_mem' := fun x _ h u a => by simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum]; rw [h]

def fixedInks (G : Gauge) (f : Ink G n → ℂ) := (fun i => (f i).re) ∈ paints G n ∧ (fun i => (f i).im) ∈ paints G n

def picker (G : Gauge) (n : ℕ) : Matrix (Ink G n) (Ink G n) ℝ :=
    let P := paints G n
    LinearMap.toMatrix' (P.subtype.comp (P.projectionOnto P.exists_isCompl.choose P.exists_isCompl.choose_spec))

lemma picks (a : Ink G n → ℝ) : picker G n *ᵥ a ∈ paints G n := by
  unfold picker; dsimp only; rw [LinearMap.toMatrix'_mulVec]; exact Subtype.coe_prop _
lemma keeps (a : Ink G n → ℝ) (h : a∈ paints G n) : picker G n *ᵥ a=a := by
  let P := paints G n
  let b : P := ⟨a,h⟩
  unfold picker; dsimp only; rw [LinearMap.toMatrix'_mulVec]; change (P.projectionOnto _ _ b.val).val= b.val; simp
lemma ink_retain (f : Ink G n → ℂ) (hp : fixedInks G f) : approached (picker G n)*ᵥ f=f := by
  funext i
  apply Complex.ext <;> simp only [Matrix.mulVec,dotProduct, Complex.re_sum,Complex.im_sum,Complex.mul_re,
    Complex.mul_im, approached,Matrix.map_apply,Complex.ofReal_im,Complex.ofReal_re,zero_mul,sub_zero,add_zero]
  exact congr_fun (keeps _ hp.1) i
  exact congr_fun (keeps _ hp.2) i

section weights
variable {α β : Type} [Fintype α] [Fintype β]
open Matrix (mulVec)

def reserve (M : Matrix β β ℝ) : ℝ := ∑ i, ∑ j, ‖M i j‖
lemma pay_reserve (M : Matrix β β ℝ) : 0 ≤ reserve M := by unfold reserve; positivity
lemma reserve_cost {R : β → Shift α → ℝ} (hr : ∀ b, Width σ A (R b)) (M : Matrix β β ℝ) (b : β) :
    Width σ (A * reserve M) (fun x => (M*ᵥ fun j => R j x) b) := by
  let f j (x : Shift α) := ‖M b j‖ * (Real.exp (σ*size x)*‖R j x‖)
  have hs j : Summable (f j) := (hr j).2.1.mul_left _
  let g x := ∑ j,f j x
  have hu : SumBudget g (A*reserve M) := by
    refine ⟨fun x => sum_nonneg fun i _ => by unfold f; positivity, summable_sum fun i _ => hs i,?_⟩
    unfold g; rw [Summable.tsum_finsetSum (fun i _ => hs i)]
    calc
      _ ≤ ∑ j, ‖M b j‖*A := sum_le_sum fun j _ => by
        unfold f; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left (hr j).2.2 (norm_nonneg _)
      _ ≤ _ := by
        have hm := hr b; rw [← Finset.sum_mul,mul_comm A]; exact mul_le_mul_of_nonneg_right
          (single_le_sum (fun i _ => sum_nonneg fun k _ => norm_nonneg _) (mem_univ b)) ((tsum_nonneg hm.1).trans hm.2.2)
  refine Work.F08.budget_minor hu (fun _ => by positivity) ?_
  intro i; unfold Matrix.mulVec dotProduct
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sum_le ..) (Real.exp_pos _).le
    _ = _ := by unfold g f; rw [Finset.mul_sum]; exact sum_congr rfl fun j _ => by dsimp; rw [abs_mul,mul_left_comm]

lemma reserve_read {R : β → Shift α → ℝ} (hr : ∀ b, Width σ A (R b)) (hσ : 0 < σ) (M : Matrix β β ℝ) (b : β)
    (p : Corn α) : readable (fun x => (M*ᵥ fun j => R j x) b) (axes p) = (approached M *ᵥ fun j => readable (R j) (axes p)) b := by
  let r := axes p
  have hv j : Width σ A (fun x => (R j x:ℂ)) := by simpa only [Width,Complex.norm_real] using hr j
  have hm j : Summable (fun i => mode r i • (R j i:ℂ)) := ((hv j).series r (by
    intro i; simp [r,axes,hσ.le])).2.1.of_norm
  have he j : Summable (fun i => (M b j:ℂ) * (mode r i * (R j i:ℂ))) := (hm j).mul_left _
  simp only [readable,Laurent.read,Matrix.mulVec,dotProduct,approached,Matrix.map_apply]
  simp_rw [← tsum_mul_left, smul_eq_mul]; rw [← Summable.tsum_finsetSum (f:=fun j i => (M b j:ℂ) * (mode (axes p) i * (R j i:ℂ))) (fun i _ => he i)]
  refine tsum_congr fun i => ?_
  push_cast; simp only [Finset.mul_sum]
  exact sum_congr rfl fun j _ => mul_left_comm ..
end weights

-- Pack for the painter
abbrev Picture (G : Gauge) (t : ℕ) := Ink G (t+1) → Run (t+1) → Space t → ℂ
abbrev Skin (G : Gauge) (t : ℕ) := CurRun (t+1) → Ink G (t+1) → Shift (Keys t) → ℝ

structure Features (f : Picture G t) (σ A : ℝ) : Prop where
    solid (x i) : Firm σ A (f x i)
    wall (x) : Contractible (f x)
    born (x i p) : star p = p → star (f x i (-p)) = f x i p
    paint (p : Corn (Keys t)) (i) : fixedInks G (fun x => f x i (axes p))

structure Shades (R : Skin G t) (f : Picture G t) (σ A : ℝ) : Prop where
    price (a i) : Width σ A (R a i)
    value p i v : fromCurl (plotted (axes p)) (fun a => readable (R a i) (axes p)) v=f i v (axes p)
    pigment (a y) : (fun i => R a i y) ∈ paints G _

private lemma div_ray {α : Type} [Fintype α] {f : Phase α → ℂ} (h : Firm σ A f) (hv : Rays n (f ∘ axes)) :
    Rays n (fun p => readable (fun x => (market f 0 x).re) (axes p)) := by
  intro p
  have he : (fun x : ℝ => star (f (-axes (x • p)))) =O[cutRay] (fun x => x^n) := by
    have H := hv (-p)
    simpa only [Function.comp_apply,isBigO_iff, smul_neg,axes_flip,norm_star] using H
  simp_rw [re_cast h (axes_real _),div_eq_inv_mul]
  exact ((hv p).add he).const_mul_left _

private def actualRate (s : ℝ) (t : ℕ) : ℝ := (2*((1+s/4)/(s/4)))^(Fintype.card (Keys t))
private lemma rate_pos (s : ℝ) (h : 0<s) (t : ℕ) : 0 ≤ actualRate s t := by unfold actualRate; positivity

private lemma insertPaint (f : Picture G t) {u v : ℝ} (h : Features f u v) (hs : 0 < σ)
    (g : Ink G (t+1) → CurRun (t+1) → Space t → ℂ)
    (hg : ∀ i j, Firm σ A (g i j)) (hf : ∀ p : Corn (Keys t), ∀ i b, fromCurl (plotted (axes p)) (fun y => g i y (axes p)) b=f i b (axes p))
    {n : ℕ} (hj : ∀ i j, Rays n (g i j ∘ axes)) :
    ∃ P : Skin G t, Shades P f (σ/2) (A*(actualRate σ t * reserve (picker G (t+1)))) ∧
      ∀ a i, Rays n (readable (P a i) ∘ axes) := by
  let M := picker G (t+1)
  let V a i (x : Shift (Keys t)) := (market (g i a) 0 x).re
  let P a i x := (M*ᵥ fun j => V a j x) i
  have hv a i : Width (σ/2) (A*actualRate σ t) (V a i) := by
    let w := hg i a
    exact Work.F07.widthRealPart (w.1.issues w.2 _ (σ/4) (by positivity) (by positivity) (by linarith))
  have hw a i p := reserve_read (hv a) (by positivity) M i p
  refine ⟨P, ⟨fun a i => ?_, fun p i b => ?_, fun a x => picks (V a · x)⟩,fun a i => ?_⟩
  · rw [← mul_assoc]; exact reserve_cost (hv a) M i
  · have he x : fromCurl (plotted (axes p)) (fun a => readable (V a x) (axes p)) b=f x b (axes p) :=
      real_rescue _ (h.born x) _ (hg x) (fun p b => hf p x b) _ _
    unfold fromCurl P
    simp_rw [hw]
    simp only [Matrix.mulVec,dotProduct, mul_sum]; rw [sum_comm]
    calc
      _ = ∑ j, (approached M i j)*(fromCurl (plotted (axes p)) (fun a => readable (V a j) (axes p)) b) := ?_
      _ = _ := ?_
    · unfold fromCurl; refine sum_congr rfl fun j _ => ?_
      rw [mul_sum]; exact sum_congr rfl fun k _ => mul_left_comm ..
    simp_rw [he]; exact congr_fun (ink_retain _ (h.paint p b)) i
  intro p
  simp only [Function.comp_apply,P]; simp_rw [hw]
  unfold Matrix.mulVec dotProduct
  apply Asymptotics.IsBigO.sum; intro j _
  exact (div_ray (hg j a) (hj j a) p).const_mul_left _

/-- Get real Laurent coefficients with *per-placement* color invariance.
Cost at fixed finite arity only. -/
lemma strokes (G : Gauge) (t : ℕ) (ht : 2 ≤ t) (σ : ℝ) (hs : 0<σ) :
    ∃ η K : ℝ, 0 < η ∧ η≤σ ∧ 0≤K ∧ ∀ (A : ℝ) (f : Picture G t), 0 ≤ A → Features f σ A →
      ∃ R : Skin G t, Shades R f η (A*K) := by
  obtain ⟨w,C,hp,hΩ,hC,H⟩ := allleg t ht σ hs
  refine ⟨w/2,C*(actualRate w t * reserve (picker G (t+1))),by positivity, by linarith,
    mul_nonneg hC (mul_nonneg (rate_pos w hp _) (pay_reserve _)), fun A f ha h => ?_⟩
  choose g hg he using fun i => H A (f i) ha (h.solid i) (h.wall i)
  obtain ⟨V,hv,_⟩ := insertPaint f h hp g hg (fun p i => he i p) (fun i j => rays_zero ((hg i j).analytic_real _))
  exact ⟨V, by rw [← mul_assoc]; exact hv⟩

lemma veins (G : Gauge) (σ : ℝ) (hs : 0<σ) : ∃ η K : ℝ, 0 < η ∧ η ≤ σ ∧ 0≤K ∧
    ∀ (A : ℝ) (s : ℕ) (f : Picture G 1), 0 ≤ A → Features f σ A →
    (∀ i j, Rays (s+2) (f i j ∘ axes)) →
    ∃ R : Skin G 1, Shades R f η (A*K) ∧ ∀ a i, Rays s (readable (R a i) ∘ axes) := by
  obtain ⟨w,C,hp,hΩ,hC,H⟩ := bothleg σ hs
  refine ⟨w/2,C*(actualRate w 1 * reserve (picker G (1+1))),by positivity, by linarith,
    mul_nonneg hC (mul_nonneg (rate_pos w hp _) (pay_reserve _)), fun A s f ha h hv => ?_⟩
  choose g hg hh he using fun i => H A s (f i) ha (h.solid i) (h.wall i) (hv i)
  rw [← mul_assoc]; exact insertPaint f h hp g hg (fun p i => he i p) hh
end YM.Stationary
end

/-! Real path presentation. Harmonic test for the loop kernel uses derivative
in p on the common series, not on the curvature inputs. Counts each of the
four plaquette edges on **every** leg. Uses actual Invariant atoms. -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Bloch Laurent Filter Finset Asymptotics
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal
variable {G : Gauge} {n t : ℕ} {σ A : ℝ}

section moments
variable {α : Type} [Fintype α] [DecidableEq α] {R : Shift α → ℝ}

omit [DecidableEq α] in
private lemma moment_bound (hw : Width σ A R) (hs : 0 < σ) : Summable fun x => ‖R x‖*(size x:ℝ) := by
  refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) (hw.2.1.mul_right σ⁻¹)
  rw [mul_right_comm, mul_comm _ ‖R x‖]; gcongr
  rw [← div_eq_mul_inv, le_div_iff₀ hs, mul_comm]; linarith [Real.add_one_le_exp (σ*size x)]

theorem vertical_moment (hw : Width σ A R) (hs : 0 < σ) (i : α) : Summable (fun x => R x*(x i:ℤ)) ∧
    HasDerivAt (fun t : ℝ => readable R (axes (t • Pi.single i (1:ℝ))))
      ((∑' x : Shift α, R x * (x i:ℤ) : ℝ) * Complex.I) 0 := by
  let Q (x : Shift α) : ℝ := R x*(x i:ℤ)
  have he : Summable (fun x : Shift α => ‖Q x‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun x => by
      unfold Q; rw [norm_mul]; gcongr
      simp only [Real.norm_eq_abs]; rw [← Int.cast_abs]; apply Int.cast_le.mpr ?_
      rw [← Int.natCast_natAbs]
      exact_mod_cast (single_le_sum (f:=fun a => (x a).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i))) (moment_bound hw hs)
  refine ⟨he.of_norm, ?_⟩
  let v (x : Shift α) (t : ℝ) := mode (axes (t • Pi.single i 1)) x
  have hz (x t) : v x t = Complex.exp ((t:ℂ)*((x i:ℤ)*Complex.I)) := by
    unfold v mode
    congr 1
    calc
      _ = Complex.I * ((axes (t • Pi.single i 1)) i * (x i:ℤ)) := by
        congr 1; rw [Finset.sum_eq_single i]
        · intro b _ hn; simp [axes,Pi.single_eq_of_ne hn]
        simp
      _ = _ := by simp [axes]; ring
  let g x t := v x t*(R x:ℂ)
  let h x t := v x t*((Q x:ℂ)*Complex.I)
  have ht x t : HasDerivAt (g x) (h x t) t := by
    unfold g h Q; simp_rw [hz]
    have hu : HasDerivAt (fun s : ℝ => (s:ℂ)) 1 t := Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    convert! ((hu.mul_const _).cexp.mul_const _) using 1; push_cast; ring
  have hh x t : ‖h x t‖ ≤ ‖Q x‖ := by unfold h v; simp [Laurent.mode_real _ x (axes_real _)]
  have hu : Summable (fun i => g i 0) := by unfold g v; simpa using (Complex.ofRealCLM.summable (hw.summable hs.le))
  have hk := hasDerivAt_tsum_of_isPreconnected he isOpen_univ isPreconnected_univ (fun x t _ => ht x t) (fun x t _ => hh x t) (Set.mem_univ _) hu (Set.mem_univ 0)
  convert! hk using 1
  unfold h v; simp [Complex.ofReal_tsum,tsum_mul_right,Q]

lemma jet_moment (hw : Width σ A R) (hs : 0<σ) (ht : Rays 2 (readable R ∘ axes)) :
    HasSum R 0 ∧ ∀ i : α, HasSum (fun x => R x*(x i:ℤ)) 0 := by
  have he := Firm.of_series (f:=fun x=> (R x:ℂ)) (A:=A) (by simpa only [Width,Complex.norm_real] using hw) hs
  have hv := he.analytic_real 0
  have hq := (rays_at_zero (f:=readable R ∘ axes) hv).1 (ht.weaker (by decide : 1≤2))
  change Laurent.read _ (axes (0:Corn α))=0 at hq
  rw [Laurent.read,axes_origin] at hq
  simp only [mode_constant,one_smul,← Complex.ofReal_tsum, Complex.ofReal_eq_zero] at hq
  refine ⟨hq ▸ (hw.summable hs.le).hasSum,fun i => ?_⟩
  obtain ⟨H,hV⟩ := vertical_moment hw hs i
  have hj := (rays_jet (f:=readable R ∘ axes) hv 2).1 ht 1 (by norm_num)
  have hy : fderiv ℝ (readable R ∘ axes) 0=0 := by
    ext1 x
    simpa [iteratedFDeriv_one_apply] using DFunLike.congr_fun hj (fun _ => x)
  have hp := Push.side (readable R ∘ axes) hv.differentiableAt (Pi.single i 1)
  rw [hy] at hp
  have hL := hV.unique hp
  change _ = (0:ℂ) at hL
  simp only [mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero] at hL
  exact hL ▸ H.hasSum
end moments

section atoms

def carrierPath (t : ℕ) [NeZero t] : ℕ ≃ CurRun (t+1) × Shift (Keys t) := by
  haveI : Nonempty (TypeFace 2) := ⟨plaquette ⟨(0,1),by decide⟩⟩
  exact enumerate _

def artery (P : Skin G t) (p : CurRun (t+1) × Shift (Keys t)) : Atom G (t+1) where
    leg i := walkSlot (plaqEquiv.symm (p.1 i)) ((Fin.cons (α:=fun _ : Fin (t+1) => Cover) (0:Cover) (fun k a => p.2 (k,a))) i)
    coeff x := P p.1 x p.2

def inkCost (G : Gauge) (t : ℕ) (σ : ℝ) := let d:=4*((t:ℝ)+1); (Fintype.card (CurRun (t+1)):ℝ)*(Fintype.card (Ink G (t+1)):ℝ)*Real.exp (σ*d)

lemma inkCost_nonneg (t : ℕ) (G : Gauge) (σ : ℝ) : 0 ≤ inkCost G t σ := by unfold inkCost; dsimp only; positivity

lemma artery_length (P : Skin G t) (q : CurRun (t+1) × Shift (Keys t)) : (artery P q).length = size q.2+4*(t+1) := by
  unfold Atom.length artery
  rw [Fin.sum_univ_succ]
  simp_rw [walkSlot_cost, Fin.cons_zero, Fin.cons_succ,sum_add_distrib, Laurent.size]
  rw [Fintype.sum_prod_type]; simp; omega

lemma realpath_price {P : Skin G t} (hp : ∀ i j, Width σ A (P i j)) :
    SumBudget (fun i => (artery P i).budget σ) (A*inkCost G t σ) := by
  let c := Real.exp (σ*(4*(t+1:ℕ):ℕ))
  let k := (Fintype.card (Ink G (t+1)):ℝ)*A*c
  have he : A*inkCost G t σ = ∑ _ : CurRun (t+1), k := by simp [inkCost,k,c]; ring
  rw [he]; apply budget_prod_finite (A:=fun _ => k)
  intro i
  let f (j : Ink G (t+1)) (x : Shift (Keys t)) := Real.exp (σ*size x)*‖P i j x‖*c
  have hh j x : 0 ≤ f j x := by unfold f c; positivity
  have hv j : Summable (f j) := (hp i j).2.1.mul_right _
  rw [show (fun x => (artery P (i,x)).budget σ)=(fun x => ∑ j,f j x) by
    ext x; rw [Atom.budget,artery_length,Atom.magnitude]
    unfold f c; simp only [artery, Nat.cast_add,mul_add,Real.exp_add,Finset.sum_mul,
      Real.norm_eq_abs]; exact sum_congr rfl fun j _ => by ring]
  refine ⟨fun x => Finset.sum_nonneg (fun j _ => hh j x), summable_sum (fun j _ => hv j),?_⟩
  rw [Summable.tsum_finsetSum (fun j _ => hv j)]
  calc
    _ ≤ ∑ _ : Ink G (t+1), A*c := sum_le_sum fun j _ => by
      unfold f; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right (hp i j).2.2 (Real.exp_pos _).le
    _ = k := by simp [k]; ring

variable [NeZero t]
def issue (P : Skin G t) (n : ℕ) := artery P (carrierPath t n)

lemma artery_funded {P : Skin G t} {f : Picture G t} (h : Shades P f σ A) :
    SumBudget (fun i => (issue P i).budget σ) (A*inkCost G t σ) ∧ ∀ i : ℕ, (issue P i).Invariant :=
    ⟨budget_copy (carrierPath t) (realpath_price h.price), fun i => (show _ from h.pigment (carrierPath t i).1 _)⟩
end atoms

lemma issue_normal {P : Skin G 1} (h : ∀ i j, Width σ A (P i j)) (hs : 0 < σ)
    (ht : ∀ a i, Rays 2 (readable (P a i) ∘ axes)) (R : PathData G) (hR : R.loop=issue P) :
    ∀ i x, HasSum (R.loop_coeff i x) 0 ∧ ∀ l : Axis, HasSum (fun k => R.loop_coeff i x k *
      (((((issue P k).leg 1).offset l - ((issue P k).leg 0).offset l : ℤ) : ℝ))) 0 := by
  intro i x
  let b : CurRun (1+1) := plaquette ∘ i
  let f (y : CurRun (1+1) × Shift (Keys 1)) : ℝ := if y.1=b then P b x y.2 else 0
  have he : R.loop_coeff i x = f ∘ (carrierPath 1) := by
    ext k
    let u := carrierPath 1 k
    have hh : ((fun j => ((R.loop k).leg j).plaq)=i) ↔ u.1=b := by
      rw [hR]
      constructor
      · intro H
        ext1 j
        exact plaqEquiv.symm.injective (show _ = plaqEquiv.symm (plaqEquiv _) by rw [plaqEquiv.symm_apply_apply]; exact congr_fun H j)
      intro H
      ext1 j
      change plaqEquiv.symm (u.1 j)= _
      rw [H]; exact plaqEquiv.symm_apply_apply _
    rw [PathData.loop_coeff]; change _=f u
    by_cases H : u.1=b
    · rw [if_pos (hh.mpr H), hR]; unfold f; rw [if_pos H]
      change P (u.1) x u.2 = _; rw [H]
    rw [if_neg (hh.not.mpr H)]; unfold f; rw [if_neg H]
  have hx {g : Shift (Keys 1) → ℝ} (h : HasSum g 0) : HasSum (fun p : CurRun (1+1) × Shift (Keys 1) => if p.1=b then g p.2 else 0) 0 := by
    let u : Shift (Keys 1) → CurRun (1+1) × Shift (Keys 1) := Prod.mk b
    have hh : Injective u := fun a b e => congr_arg Prod.snd e
    refine (Function.Injective.hasSum_iff hh ?_).1 ?_
    · intro i hi; apply if_neg; intro he; exact hi ⟨i.2, Prod.ext he.symm rfl⟩
    simpa only [u,Function.comp_def,↓reduceIte] using! h
  obtain ⟨H,H'⟩ := jet_moment (h b x) hs (ht b x)
  rw [he]; refine ⟨(carrierPath 1).hasSum_iff.mpr (hx H), fun l => ?_⟩
  apply HasSum.congr_fun ((carrierPath 1).hasSum_iff.mpr (hx (H' (0,l)))) (fun n => ?_)
  let v := carrierPath 1 n
  symm
  change (if v.1=b then P b x v.2*(v.2 (0,l):ℤ) else 0) = f v * _
  simp only [issue,artery,Fin.cons_zero,walkSlot_end]
  unfold f; split
  · congr 2
    change _ = v.2 (0,l)-0; simp
  simp
end YM.Stationary
end

/-! # Wave normalization for the scalar jets

`Recorded` uses a coefficient (normalized by n!), complex-linear in wave amplitudes
(not Hermitian form except by supplying conjugated tests), with inverse-momentum
slot *first* in n=2. `volume` at this calculation is the CARD of target sites,
using counting Fourier conventions; not a Haar probability divisor.
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset Asymptotics
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal
variable {G : Gauge} {n t : ℕ} {m : Side}

section identify
variable (G m) (n : ℕ)

abbrev Loc (G : Gauge) (n : ℕ) := TypeFace n × G.ColorIndex
abbrev Lines (G : Gauge) (m : Side) (n : ℕ) := Co m (Loc G n)

def arm : Corn (Lines G m n) ≃L[ℝ] fieldDir G m n := LinearEquiv.toContinuousLinearEquiv {
    toFun a x := WithLp.toLp 2 fun i => a (x.1,x.2,i)
    invFun a x := a (x.1,x.2.1) x.2.2
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    left_inv _ := rfl
    right_inv _ := rfl }
lemma arm_apply (x : Corn (Lines G m n)) (i j k) : arm G m n x (i,j) k=x (i,j,k) := rfl

def input (a : Corn (Lines G m 1)) := represent (arm G m 1 a)
@[simp] lemma input_zero : input G m 0=1 := by unfold input; rw [map_zero,link_one]
lemma inverts (F H : fieldDir G m 1 → ℝ) (p : ℕ) (hf : ContDiffAt ℝ ω F 0) (hu : ContDiffAt ℝ ω H 0)
    (hh : iteratedFDeriv ℝ p (F ∘ arm G m 1) 0=iteratedFDeriv ℝ p (H ∘ arm G m 1) 0) :
    iteratedFDeriv ℝ p F 0=iteratedFDeriv ℝ p H 0 := by
  ext1 v
  let L := (arm G m 1).toContinuousLinearMap
  have he := DFunLike.congr_fun hh (fun i => (arm G m 1).symm (v i))
  change iteratedFDeriv ℝ p (F ∘ L) 0 _=iteratedFDeriv ℝ p (H ∘ L) 0 _ at he
  rw [wired L ?_, wired L ?_, map_zero] at he
  · simpa [L,Function.comp_def] using he
  all_goals rw [map_zero]
  exacts [hu.analyticAt,hf.analyticAt]
end identify

section mesh
variable {α : Type} [Fintype α] [DecidableEq α]

def tune (p : Site m) (v : Phase α) : Phase (Co m α) := fun i => cell p i.1 * v i.2

def relay (p : Site m) (a : α) : Phase (Co m α) := tune p (Pi.single a 1)
omit [Fintype α] in
lemma coef_wave (p x : Site m) (i j : α) : rotations m α (x,i) (p,j) = relay p j (x,i) := by
  by_cases h : i=j <;> simp [rotations,relay,tune, *]
lemma relay_ext {ι : Type} [Fintype ι] [DecidableEq ι] (F H : RecordM ℂ ι (Co m α))
    (he : ∀ (p : ι → Co m α), F (fun i => relay (p i).1 (p i).2) = H fun i => relay (p i).1 (p i).2) : F=H := by
  let L := rotations m α
  let d := (m.val:ℂ)^4
  have hp : d≠0 := pow_ne_zero 4 (side_ne _)
  apply MultilinearMap.ext; intro v
  let b (i : ι) := d⁻¹ • (star L *ᵥ v i)
  have ht (i : ι) : L *ᵥ b i = v i := by
    rw [show b i=_ from rfl, Matrix.mulVec_smul, Matrix.mulVec_mulVec, rotations_gram]
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]; exact inv_smul_smul₀ hp _
  let g (i : ι) (k : Co m α) := b i k • relay k.1 k.2
  have hW : v=(fun i => ∑ j,g i j) := by
    funext i z; rw [← ht i, Finset.sum_apply, Matrix.mulVec, dotProduct]
    exact sum_congr rfl fun p _ => (congrArg (· * b i p) (coef_wave p.1 z.1 z.2 p.2)).trans (mul_comm ..)
  rw [hW,F.map_sum (g:=g),H.map_sum (g:=g)]
  refine sum_congr rfl fun j _ => ?_
  rw [show F _=_ from F.map_smul_univ (fun i => b i (j i)) _,show H (fun i => g i (j i)) = _ from H.map_smul_univ (fun i => b i (j i)) (fun i => relay _ _),he]

-- Momentum conservation exact, even aliases at −π
lemma profile_shift (p : Fin (t+1) → Site m) (hp : ∑ i,p i=0) :
    p 0 = -∑ i : Fin t, p i.succ := by
  rw [Fin.sum_univ_succ] at hp; exact eq_neg_of_add_eq_zero_left hp

def outphase (p : Fin (t+1) → Site m) : Space t := fun i => mon (p i.1.succ) i.2
lemma out_real (p : Fin (t+1) → Site m) : star (outphase p)=outphase p := funext fun ⟨i,j⟩ => congr_fun (real_frequency (p i.succ)) j
lemma manyModes (p : Fin (t+1) → Site m) (hp : ∑ i,p i=0) (x : Cover) (j : Fin (t+1)) :
    mode (plotted (outphase p) j) x=cell (p j) (wrap m x) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [profile_shift p hp,cell_duality]
    simp only [plotted,Fin.cons_zero,missing]
    rw [mode_inverse,cell_inverse]
    let s (i : Fin t) := p i.succ
    congr 1
    suffices hh : ∀ k : Finset (Fin t), mode (∑ i ∈ k,mon (s i)) x = cell (wrap m x) (∑ i∈k, s i) from hh univ
    intro k; induction k using Finset.induction with
    | empty => simp
    | insert i u hv ih =>
      rw [sum_insert hv,sum_insert hv,cell_add,mode_phase,ih,cell_duality _ (s i),cell_wrap]
  simp only [plotted, Fin.cons_succ,cell_wrap]; rfl

lemma waved_symbol (p : Fin (t+1) → Site m) (hp : ∑ i,p i=0) (j k) :
    symbol k (plotted (outphase p) j)=symbol k (mon (p j)) := by
  simp only [← reading,Row.read,Laurent.read]
  simp_rw [manyModes p hp,cell_wrap]
end mesh

-- Denominator volume (coarse for blocked, fine for unblocked).
def glyph (p : Fin (t+1) → Site m) (i : Ink G (t+1)) (b : Run (t+1)) : Fin (t+1) → Phase (Lines G m 1) := fun a => relay (p a) (b a,i a)

def collected (L : Picture G t) (p : Fin (t+1) → Site m) (i b) :=
    if ∑ j, p j=0 then (Fintype.card (Site m):ℂ)*L i b (outphase p) else 0

/-- A complex per-lattice bill on the coefficient. To specify per-site normalized,
multiply by cardinality in the caller. It will pay all amplitudes in comparison
but here only prices the canonical unit-amplitude basis. -/
def Recorded (L : Picture G t) (f : Corn (Lines G m 1) → ℝ) (A : ℝ) := ∀ p i b,
    ‖noteAt f (t+1) (glyph (m:=m) p i b) - collected L p i b‖ ≤ A
end YM.Stationary
end

/-! Ordered curvature tensor, leading part of the actual uncut atom series. -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset Asymptotics
open Matrix (transpose mulVec of)
open scoped Matrix Matrix.Norms.Frobenius Topology ContDiff BigOperators NNReal
variable {G : Gauge} {n t : ℕ} {m : Side}

abbrev Link (G : Gauge) (m : Side) := Corn (Lines G m 1)

def plaqEval (p : Face (Per m)) (b : G.ColorIndex) : Link G m →L[ℝ] ℝ := LinearMap.toContinuousLinearMap {
    toFun a := Work.F03.faceCurl p (arm G m 1 a) b
    map_add' x y := congr_fun (Matrix.mulVec_add (d 1 m) (parts _ 1 (arm G m 1 x) b) (parts _ 1 (arm G m 1 y) b)) _
    map_smul' c x := congr_fun (Matrix.mulVec_smul (d 1 m) c (parts _ 1 (arm G m 1 x) b)) _ }

def inkNote (p : Site m) (A : Atom G n) : Tensor.T (Link G m) ℝ n := ∑ x : Ink G n,
    (ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (A.coeff x)).compContinuousLinearMap
      (fun j => plaqEval (Work.F03.slotFace (A.leg j) p) (x j))

lemma ink_note (p : Site m) (A : Atom G n) (v : Fin n → Link G m) :
    inkNote p A v = ∑ x : Ink G n, A.coeff x *
      ∏ j : Fin n, Work.F03.faceCurl (Work.F03.slotFace (A.leg j) p) (arm G m 1 (v j)) (x j) := by
  unfold inkNote; rw [_root_.sum_apply]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_comm (A.coeff j)]; rfl

private def payFixed (G : Gauge) (m : Side) := ∑ p : Face (Per m), ∑ b : G.ColorIndex, ‖plaqEval p b‖

lemma ink_budget (p : Site m) (A : Atom G n) : ‖inkNote p A‖ ≤ A.magnitude * payFixed G m ^ n := by
  rw [inkNote, Atom.magnitude, Finset.sum_mul]
  apply (norm_sum_le ..).trans (Finset.sum_le_sum ?_)
  intro x _
  have h (i : Fin n) : ‖plaqEval (Work.F03.slotFace (A.leg i) p) (x i)‖ ≤ payFixed G m :=
    (single_le_sum (f:=fun j => ‖plaqEval (Work.F03.slotFace (A.leg i) p) j‖) (fun _ _ => norm_nonneg _) (mem_univ (x i))).trans
      (single_le_sum (f:=fun p : Face (Per m) => ∑ b : G.ColorIndex, ‖plaqEval p b‖) (fun k _ => sum_nonneg fun j _ => norm_nonneg _) (mem_univ _))
  refine ContinuousMultilinearMap.opNorm_le_bound (by unfold payFixed; positivity) (fun v => ?_)
  change ‖(∏ i, plaqEval (Work.F03.slotFace (A.leg i) p) (x i) (v i)) * A.coeff x‖ ≤ _
  rw [norm_mul,norm_prod]
  calc
    _ ≤ (∏ i, payFixed G m * ‖v i‖) * ‖A.coeff x‖ := by
      refine mul_le_mul_of_nonneg_right (prod_le_prod (fun i _ => norm_nonneg _) ?_) (norm_nonneg _)
      exact fun i _ => (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (h i) (norm_nonneg _))
    _ = _ := by simp [prod_mul_distrib]; ring

section order
variable (m) (F : ℕ → Atom G n)

def seriesScore (a : Link G m) := uncut F (input G m a)
def volumeInk := ∑ x : Site m, ∑' i, inkNote x (F i)

variable {σ C : ℝ} (hs : 0<σ) (h : SumBudget (fun i => (F i).budget σ) C)
include hs h

lemma ink_summable p : Summable (fun i => ‖inkNote (m:=m) p (F i)‖) := Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun i => (ink_budget p (F i)).trans (mul_le_mul_of_nonneg_right
        ((F i).lower_budget σ hs) (by unfold payFixed; positivity))) (h.2.1.mul_right _)

lemma ink_apply (v : Fin n → Link G m) : volumeInk m F v = ∑ x : Site m, ∑' i, inkNote x (F i) v := by
  unfold volumeInk; rw [_root_.sum_apply]; refine sum_congr rfl fun i _ => ?_
  exact (ContinuousMultilinearMap.apply ℝ _ ℝ v).map_tsum (ink_summable m F hs h i).of_norm

lemma path_lim (v : Link G m) : Tendsto (fun b : ℝ => (b^n)⁻¹ • seriesScore m F (b • v)) cutRay
    (𝓝 (Tensor.diagonal (volumeInk m F) v)) := by
  unfold Tensor.diagonal; rw [ink_apply m F hs h]; simp_rw [ink_note]
  have hv := Work.F03.atoms_limit (arm G m 1 v) F hs h
  simpa only [seriesScore,input,map_smul, Atom.poly,div_eq_inv_mul,smul_eq_mul] using hv

lemma score_analytic : AnalyticAt ℝ (seriesScore m F) 0 :=
    (Work.F02.uncut_contDiffAt (A:=input G m) hs h (fun i =>
      (Work.F03.represent_smooth (G:=G) i).contDiffAt.comp (f:=arm G m 1) _ (arm G m 1).contDiff.contDiffAt)).analyticAt
lemma ink_low : Rays n (seriesScore m F) := ray_origin (fun v => ⟨_,path_lim m F hs h v⟩)

lemma total_ink : Tensor.coeff (seriesScore m F) n 0 = Tensor.symmetrize (volumeInk m F) := by
  have he := score_analytic m F hs h
  apply Tensor.ext_diag _ _ (Tensor.coeff_symm he.contDiffAt) (Tensor.symmetrize_sym _)
  funext p; simp only [Tensor.symmetrize_diagonal]
  exact tendsto_nhds_unique (ray_limit he (ink_low m F hs h) p) (path_lim m F hs h p)

/-- Keep the symmetric permutation in each dot product. -/
lemma ink_beat (v : Fin n → Phase (Lines G m 1)) :
    noteAt (seriesScore m F) n v= (n.factorial:ℂ)⁻¹ * ∑ p : Equiv.Perm (Fin n), enlarge (volumeInk m F).toMultilinearMap (v ∘ p) := by
  let L := enlarge (volumeInk m F).toMultilinearMap
  let M := ∑ p : Equiv.Perm (Fin n), ((n.factorial:ℂ)⁻¹) • L.domDomCongr p
  suffices he : noteAt (seriesScore m F) n = M by
    rw [he, Finset.mul_sum]; unfold M; rw [_root_.sum_apply]; rfl
  apply enlarge_unique; intro v
  rw [note_map,total_ink m F hs h,enlarge_real]
  unfold M L; rw [_root_.sum_apply]; simp only [_root_.smul_apply,Tensor.symmetrize]
  change (((Fintype.card (Equiv.Perm (Fin n)):ℝ)⁻¹ *
    (∑ p : Equiv.Perm (Fin n), (volumeInk m F).domDomCongr p) v : ℝ): ℂ)=_
  rw [_root_.sum_apply]; push_cast
  rw [Fintype.card_perm, Fintype.card_fin,Finset.mul_sum]
  refine sum_congr rfl fun i _ => ?_
  change _ = _ * enlarge _ (axes ∘ (v ∘ i)); rw [enlarge_real]; rfl
end order
end YM.Stationary
end

/-! # The actual periodic test of the paths, including n=2 harmonic -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset Asymptotics
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal
variable {G : Gauge} {n t : ℕ} {m : Side} {σ A : ℝ}

-- moving sums through complexified tensors
section summable
variable {α : Type} [Fintype α] [DecidableEq α]
lemma enlarge_sum {ι : Type} (s : Finset ι) (F : ι → Tensor.T (Corn α) ℝ n)
    (b : Fin n → Phase α) : enlarge (∑ i ∈ s, F i).toMultilinearMap b = ∑ i∈s, enlarge (F i).toMultilinearMap b := by
  let Q := ∑ i∈s,enlarge (F i).toMultilinearMap
  have he : enlarge (∑ i∈s,F i).toMultilinearMap=Q := by
    apply enlarge_unique; intro v
    rw [enlarge_real]; unfold Q; rw [_root_.sum_apply]; simp_rw [enlarge_real]
    simp
  rw [he]; unfold Q; rw [_root_.sum_apply]

lemma enlarge_series {ι : Type} (F : ι → Tensor.T (Corn α) ℝ n) (hf : Summable F)
    (b : Fin n → Phase α) : HasSum (fun i => enlarge (F i).toMultilinearMap b) (enlarge (tsum F).toMultilinearMap b) := by
  let u : Tensor.T (Corn α) ℝ n →ₗ[ℝ] ℂ := {
    toFun x := enlarge x.toMultilinearMap b
    map_add' x y := by
      unfold enlarge; rw [recording_apply,recording_apply,recording_apply]; simp_rw [← sum_add_distrib]
      apply sum_congr rfl; intro i _; simp [mul_add]
    map_smul' a x := by
      unfold enlarge; rw [recording_apply,recording_apply]; simp [Finset.smul_sum]
      apply sum_congr rfl; intro i _; ring }
  exact LinearMap.toContinuousLinearMap u |>.hasSum hf.hasSum
end summable

-- slot Hessian tests

def faceParts (j : G.ColorIndex) : Phase (Lines G m 1) →ₗ[ℂ] (Co m (TypeFace 1) → ℂ) := LinearMap.pi fun p => LinearMap.proj (p.1,p.2,j)

def faceStamp (p : Face (Per m)) (i : G.ColorIndex) : Phase (Lines G m 1) →ₗ[ℂ] ℂ :=
    LinearMap.proj (p.1,plaquette p.2) ∘ₗ Matrix.mulVecLin (approached (d 1 m)) ∘ₗ faceParts i

lemma faceReal (p : Face (Per m)) (i) (v : Link G m) :
    faceStamp p i (axes v) = ↑((Work.F03.faceCurl p (arm G m 1 v)) i) := by
  change (approached (d 1 m) *ᵥ (fun x : Body 1 m => ((v (x.1,x.2,i)):ℂ))) (p.1,plaquette _) =
    (((d 1 m *ᵥ _) (p.1,plaquette _):ℝ):ℂ)
  simp only [Matrix.mulVec,dotProduct, Complex.ofReal_sum,Complex.ofReal_mul]; rfl

lemma stamp_tone (p : Face (Per m)) (i b : G.ColorIndex) (a : Site m) (k : TypeFace 1) :
    faceStamp p i (relay a (k,b)) = if b=i then cell a p.1 * symbol 1 (mon a) (plaquette p.2) k else 0 := by
  change (approached (d 1 m) *ᵥ faceParts _ _) _=_
  split; next hb =>
    subst b
    have he : faceParts i (relay a (k,i))=fun x => rotations m _ x (a,k) := by
      funext x; rw [show x=(x.1,x.2) from rfl, coef_wave]
      simp [faceParts,relay,tune, Pi.single_apply]
    rw [he]
    change (approached (d 1 m)* rotations m (TypeFace 1)) _ _=_
    rw [show d 1 m = _ from rfl, circulant m (cobound 1) (cobound_safe _), rot_fiber, reading]
  next h =>
    rw [show faceParts i (relay a (k,b))=0 by
      funext j; simp [faceParts,relay,tune, Ne.symm h], Matrix.mulVec_zero]; rfl

lemma ink_order (p : Site m) (a : Atom G n) (b : Fin n → Phase (Lines G m 1)) :
    enlarge (inkNote p a).toMultilinearMap b = ∑ y : Ink G n, (a.coeff y:ℂ)*
      ∏ j, faceStamp (Work.F03.slotFace (a.leg j) p) (y j) (b j) := by
  let T (y : Ink G n) : RecordM ℂ (Fin n) (Lines G m 1) :=
      (MultilinearMap.mkPiRing ℂ (Fin n) (a.coeff y:ℂ)).compLinearMap (fun j => faceStamp (Work.F03.slotFace (a.leg j) p) (y j))
  have hz (v y) : T y v = (a.coeff y:ℂ)*∏ j, faceStamp (Work.F03.slotFace (a.leg j) p) (y j) (v j) := by rw [mul_comm]; rfl
  suffices he : enlarge (inkNote p a).toMultilinearMap= ∑ y,T y by rw [he,_root_.sum_apply]; simp_rw [hz]
  apply enlarge_unique; intro v
  rw [enlarge_real,_root_.sum_apply]; simp_rw [hz,Function.comp_apply,faceReal]
  change ((inkNote p a v:ℝ):ℂ)=_
  rw [ink_note]; push_cast; rfl

lemma ink_atom_wave (a : Atom G (t+1)) (x : Site m) (p : Fin (t+1) → Site m) (u i) :
    enlarge (inkNote x a).toMultilinearMap (glyph p u i) =
      (a.coeff u:ℂ) * ∏ j, cell (p j) (wrap m (a.leg j).offset+x) * symbol 1 (mon (p j)) (plaquette (a.leg j).plaq) (i j) := by
  rw [ink_order]
  unfold glyph
  simp_rw [stamp_tone]
  rw [sum_eq_single u]
  · simp [Work.F03.slotFace]
  · intro b hb he
    have he : ∃ k, u k ≠ b k := by by_contra! h; exact he (funext h).symm
    obtain ⟨k,hk⟩ := he
    rw [prod_eq_zero (mem_univ k),mul_zero]; rw [if_neg hk]
  simp

lemma volume_wave (F : ℕ → Atom G (t+1)) (hw : 0 < σ) (H : SumBudget (fun i => (F i).budget σ) A)
    (p : Fin (t+1) → Site m) (v i) :
    enlarge (volumeInk m F).toMultilinearMap (glyph p v i)=
      if ∑ j, p j=0 then
        (Fintype.card (Site m):ℂ) * ∑' n, enlarge (inkNote 0 (F n)).toMultilinearMap (glyph p v i) else 0 := by
  unfold volumeInk
  rw [enlarge_sum]
  let a := ∑ j,p j
  let K := ∑' n, enlarge (inkNote 0 (F n)).toMultilinearMap (glyph p v i)
  have he (x : Site m) : enlarge (∑' n,inkNote x (F n)).toMultilinearMap (glyph p v i) = cell a x * K := by
    have hm := ink_summable m F hw H x
    rw [← (enlarge_series _ hm.of_norm _).tsum_eq]
    unfold K
    rw [← tsum_mul_left]; refine tsum_congr fun n => ?_
    simp only [ink_atom_wave, cell_add, cell_origin,mul_one]
    have hh : cell a x = ∏ j,cell (p j) x := by
      suffices hh : ∀ s : Finset (Fin (t+1)), cell (∑ j∈s,p j) x = ∏ j∈s,cell (p j) x from hh univ
      intro s; induction s using Finset.induction with
      | empty => simp [cell_duality _ x]
      | insert i s h IH => rw [sum_insert h,prod_insert h,cell_duality _ x,cell_add,cell_duality x,cell_duality x,IH]
    simp only [prod_mul_distrib,hh]; ring
  simp_rw [he, ← Finset.sum_mul]
  change (∑ x,cell a x)*K=if a=0 then _*K else 0
  split
  next h => rw [h]; simp [cell]
  next h => rw [sum_cell h,zero_mul]

lemma notesPath [NeZero t] {P : Skin G t} {f : Picture G t} (hs : 0<σ) (h : Shades P f σ A) (p : Fin (t+1) → Site m) (v i) :
    enlarge (volumeInk m (issue P)).toMultilinearMap (glyph p v i) = collected f p v i := by
  rw [volume_wave _ hs (artery_funded h).1, collected]; split; swap; rfl
  rename_i hp
  congr 1
  have he q (y) : mode (outphase p) y = ∏ j, cell (p j) (wrap m ((artery P (q,y)).leg j).offset) := by
    simp only [cell_wrap,artery,walkSlot_end,Fin.prod_univ_succ,Fin.cons_zero,mode_zero,one_mul,Fin.cons_succ]
    unfold mode; rw [Fintype.sum_prod_type, Finset.mul_sum, Complex.exp_sum]; rfl
  let a := outphase p
  have hh : star a=a := out_real p
  have ha : ∃ r : Corn (Keys t), axes r=a := ⟨_,axes_of_real hh⟩
  obtain ⟨r,Hr⟩ := ha
  have hy := h.value r v i; rw [Hr] at hy
  rw [← show a=outphase p from rfl,← hy]
  let L (x : CurRun (t+1) × Shift (Keys t)) := enlarge (inkNote 0 (artery P x)).toMultilinearMap (glyph p v i)
  change ∑' n, L (carrierPath t n)= _
  rw [(carrierPath t).tsum_eq]
  have hL : Summable L := by
    apply (carrierPath t).summable_iff.mp
    exact (enlarge_series _ (ink_summable m _ hs (artery_funded h).1 0).of_norm _).summable
  rw [hL.tsum_prod, tsum_fintype, fromCurl]
  apply sum_congr rfl; intro j _
  unfold readable Laurent.read; rw [← tsum_mul_left]; refine tsum_congr fun b => ?_
  unfold L
  rw [ink_atom_wave, he j b, prod_mul_distrib]
  simp [waved_symbol p hp,artery,a,cell_wrap]
  simp_rw [show ∀ (x : Cover) (y : TypeFace 2),plaquette (walkSlot (plaqEquiv.symm y) x).plaq=y from fun x y => plaqEquiv.apply_symm_apply _]; ring
end YM.Stationary
end
