import YM.Next.STATIONARY.Spectral.Folding


set_option autoImplicit false
/-! # Receipts for the three classical vertices before evaluating at scale L

Output-wise costs for following the induction involve two registers:
linear base width and the working-age σ. We keep them distinct. -/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Asymptotics Laurent Lattice Exterior Bloch Precision RG Wilson
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius
variable {G : Gauge} {σ A : ℝ} {t s : ℕ}

section
variable {m : ℕ→Side} {F : ∀ i, Link G (m i)→ℝ}

lemma LawfulSum.mono' (h : LawfulSum s m F t) {u : ℕ} (hu : u ≤ s) : LawfulSum u m F t := by
  obtain ⟨L,Hx,hp,hy⟩ := h; exact ⟨L,Hx,hp,fun i j => (hy i j).weaker hu⟩

/-- Loss in the soft power (not in the price). Uniform analyticity may *not*
be concluded directly from Ward. -/
theorem pure_white (ha : Tendsto (fun i => (m i).val) atTop atTop) (hf : ∀ i, Pointwise (F i))
    (h0 : ∀ i, fderiv ℝ (F i) 0=0) (hs : LawfulSum 2 m F 1)
    (p : Picture G 2) (hp : ∀ i j, Firm σ A (p i j)) (h : ∀ i, Recorded p (F i) 0) : ∀ i j,Rays 1 (p i j ∘ axes) := by
  intro i j; apply rayDark i j (by norm_num) hp (fun i j k => full_ring i j k ha p hp h (fun i => (hf i).analytic) h0 (fun l hl he => by rw [show l=1 by omega]; exact hs) (fun i => (hf i).guard))

theorem pure_grey (ha : Tendsto (fun i => (m i).val) atTop atTop) (hf : ∀ i, Pointwise (F i))
    (h0 : ∀ i, fderiv ℝ (F i) 0=0) (hs : LawfulSum 3 m F 1)
    {q u : ℝ} (p : Picture G 2) (v : Picture G 3) (hp : ∀ i j, Firm σ A (p i j)) (h : ∀ i, Recorded p (F i) 0)
    (hx : ∀ i j, Firm q u (v i j)) (hv : ∀ i, Recorded v (F i) 0) :
     (∀ i j,Rays 2 (p i j ∘ axes)) ∧ ∀ i j,Rays 1 (v i j ∘ axes) := by
  have he (i) (j) := rayBlack i j (by decide : 2 ≤ 2) hp (fun i j k => full_ring i j k ha p hp h (fun i => (hf i).analytic) h0 (fun l hl he => by rw [show l=1 by omega]; exact hs) (fun i => (hf i).guard))
  refine ⟨he,fun i j => rayDark i j (by decide : 0 < 3) hx (fun i j k => ?_)⟩
  apply full_ring _ _ _ ha v hx hv (fun i => (hf i).analytic) h0 _ (fun i => (hf i).guard)
  intro a ha hb
  interval_cases a
  · exact hs.mono' (by decide)
  exact ⟨p,⟨σ,A,hp⟩,h,he⟩

lemma whites_on_K {p : Clip} {X : PathData G} {B : Bed} {k w s τ C a b : ℝ}
    (hf : X.Bounds p s τ C) (hw : Attached B X) (hc : B.metric.strip k w) (hk : 0<k) (he : ∀ i, Floor B p (m i) a b)
    (hS : ∀ i, Bid.Sworn B (m i) G) (E : ∀ i,F i=inputSeries p X (m:=m i)) : LawfulSum 2 m F 1 ∧
        LawfulSum 3 m (F - (fun i => WilsonQ G (m i))) 1 := by
  let J := slots B.metric G
  have H i : Recorded J (F i) 0 := by rw [E]; exact according (B.metric.rights k w hc hk.le) (low_columns hf hw (he i) (hS i)).2.2
  have hx i : AnalyticAt ℝ (F i) 0 := by rw [E]; exact (stain_knit X p hf).analytic
  have hr i j := slots_cost (G:=G) hk hc i j
  have hy : LawfulSum 2 m F 1 := ⟨J,⟨_,_,hr⟩,H, fun i j => bed_rays hk hc i j⟩
  refine ⟨hy,J-slots leader G, ⟨_,_,fun i j => (hr i j).sub (slots_cost hk (leader_pay k) i j)⟩,fun i =>
    (H i).less (hx i) Wilson_witness.analytic (outright G (m i)).2.2,fun i j => ?_⟩
  exact slots_gain hk hc (he 0).starts i j
end

/-- Two key tests for the pure classical curvature terms making the induction
possible. `w` later attained using this SAME chart family, not a specified
solution of the beta recurrence. -/
theorem extra_curves (G : Gauge) (σ : ℝ) (h : 0<σ) : ∃ η K, 0<η ∧ 0≤K ∧
    ∀ m : ℕ→ Side, Tendsto (fun i => (m i).val) atTop atTop →
    ∀ (X : ℕ→Atom G 3) (V : ℕ→Atom G 4) (A : ℝ), 0 ≤ A → AtomWall X σ A → AtomWall V σ A →
    ∃ L : Picture G 2, ∃ M : Picture G 3,
      let F := fun i : ℕ => turnSeries X (m:=m i)+turnSeries V
      (∀ i j, Firm η (A*K) (L i j) ∧ Rays 2 (L i j ∘ axes)) ∧ (∀ i j, Firm η (A*K) (M i j) ∧ Rays 1 (M i j ∘ axes)) ∧
      ∀ i, Recorded L (F i) 0 ∧ Recorded M (F i) 0 := by
  obtain ⟨x₁,K₁,h₁,g₁,H⟩ := orbit_cost G 3 2 h
  obtain ⟨x₂,K₂,h₂,g₂,U⟩ := orbit_cost G 3 3 h
  obtain ⟨x₃,K₃,h₃,g₃,L⟩ := orbit_cost G 4 2 h
  obtain ⟨x₄,K₄,h₄,g₄,V⟩ := orbit_cost G 4 3 h
  let η := min (min x₁ x₂) (min x₃ x₄)
  let K := K₁+K₂+K₃+K₄
  have hu : 0 < η := lt_min (lt_min h₁ h₂) (lt_min h₃ h₄)
  have hη : η≤min x₁ x₂ := min_le_left ..; have hΩ : η ≤ min x₃ x₄ := min_le_right ..
  refine ⟨η,K,hu,by unfold K; positivity,fun m hm X Y A hp hX hY => ?_⟩
  obtain ⟨A₁,H₁,I⟩ := H _ _ hX.1
  obtain ⟨A₂,H₂,J⟩ := U _ _ hX.1
  obtain ⟨A₃,H₃,B⟩ := L _ _ hY.1
  obtain ⟨A₄,H₄,C⟩ := V _ _ hY.1
  let F i := turnSeries X (m:=m i)+turnSeries Y
  have hx (i : Side) := stain_ink X h hX.1 hX.2 (m:=i); have hy (i : Side) := stain_ink Y h hY.1 hY.2 (m:=i)
  have ha (i) : Pointwise (F i) := (hx _).add (hy _)
  let p := A₁+A₃
  let q := A₂+A₄
  have hF (i) : Recorded p (F i) 0 := (I _).both (hx _).analytic (hy _).analytic (B _)
  have hG (i) : Recorded q (F i) 0 := (J _).both (hx _).analytic (hy _).analytic (C _)
  have ht i j : Firm η (A*K) (p i j) := by
    apply (((H₁ i j).mono hu (hη.trans (min_le_left ..)) le_rfl).add ((H₃ i j).mono hu (hΩ.trans (min_le_left ..)) le_rfl)).mono hu le_rfl
    rw [← mul_add]; gcongr; unfold K; linarith
  have hb i j : Firm η (A*K) (q i j) := by
    apply (((H₂ i j).mono hu (hη.trans (min_le_right ..)) le_rfl).add ((H₄ i j).mono hu (hΩ.trans (min_le_right ..)) le_rfl)).mono hu le_rfl
    rw [← mul_add]; gcongr; unfold K; linarith
  have he (i : ℕ) : Rays 3 (F i) := (turns_low X (m:=_) h hX.1).add ((turns_low Y (m:=_) h hY.1).weaker (by decide : 3 ≤ 4))
  have hz i : fderiv ℝ (F i) 0=0 := by
    ext1 x
    simpa using DFunLike.congr_fun ((rays_jet (ha i).analytic 3).1 (he i) 1 (by decide)) ![x]
  have hs : LawfulSum 3 m F 1 := by
    refine ⟨0,⟨η,0,fun i j => Firm.zero hu⟩,fun i => ?_,fun i j b => isBigO_zero ..⟩
    have hu := (rays_jet (ha i).analytic 3).1 (he i) 2 (by decide)
    apply (record_exact ..).2; intro v w b
    rw [noteAt, beat, show iteratedFDeriv ℝ (1+1) (F i) 0=0 from hu]
    unfold collected enlarge; split <;> simp [recording_apply]
  obtain ⟨hv,hw⟩ := pure_grey hm ha hz hs p q ht hF hb hG
  exact ⟨p,q,fun i j => ⟨ht i j,hv i j⟩,fun i j => ⟨hb i j,hw i j⟩,fun i => ⟨hF i,hG i⟩⟩
end YM.Stationary
end

/-!
Soft kernel → position/difference presentation. One division per POWER,
not per scale. Over two slots may push any indicated q's from the right
leg across to left (analytic adjoint, not conjugating at complex phases).
-/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Asymptotics Laurent Lattice Exterior Bloch Precision RG Wilson
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius
variable {G : Gauge} {σ A : ℝ} {n t : ℕ} {α : Type} [Fintype α] [DecidableEq α]

private def evalSmall (i : α) (p : Phase α) := update p i 0

private lemma rays_cut (u : α) {f : Phase α → ℂ} (h : Rays n (f ∘ axes)) :
    Rays n (f ∘ evalSmall u ∘ axes) := by
  intro p
  apply (h (update p u 0)).congr_left
  intro x; change f _ = f _; congr 1
  ext1 j; unfold evalSmall; by_cases H : j=u <;> simp [*,axes]

def staged (J : Finset α) (p : Phase α) : Phase α := fun i => if i∈J then 0 else p i

private lemma sustain (hσ : 0<σ) (ha : 0≤A) (J : Finset α) (f : Phase α→ ℂ) (hf : Firm σ A f) (hp : Rays (n+1) (f ∘ axes)) :
    ∃ g : α → Phase α→ℂ, (∀ j,Firm (σ/4) (A*priceDivision α σ) (g j) ∧ Rays n (g j ∘ axes)) ∧
      ∀ p∈strip (σ/4), f p-f (staged J p)=∑ j∈J, divZ j p*g j p := by
  have ht : 0 ≤ A*priceDivision α σ := mul_nonneg ha (priceDivision_pos _ hσ _).le
  have he : 0 < σ/4 := by positivity
  induction J using Finset.induction_on generalizing f with
  | empty => refine ⟨fun _ _ => 0,fun j => ⟨(Firm.zero he).mono he le_rfl ht, fun _ => isBigO_zero ..⟩,fun p hp => by simp [show staged (α:=α) ∅ p=p from funext fun i => if_neg (Finset.notMem_empty _)]⟩
  | @insert i s hs ih =>
    obtain ⟨u,hu,H⟩ := div_var i hf
    have hU : Rays n (u ∘ axes) := rays_div hu hp (fun p => H (axes p) (hu.in_range (axes_real _)))
    obtain ⟨g,hg,Y⟩ := ih (f ∘ evalSmall i) (divCost i hf) (rays_cut i hp)
    refine ⟨update g i u,fun j => ?_,fun p hp => ?_⟩
    · by_cases h : j=i; simpa [h] using And.intro hu hU
      simp only [update_of_ne h]; exact hg _
    rw [sum_insert hs, update_self,H p hp,
      show (∑ j∈s, divZ j p*update g i u j p) = _ from
        (sum_congr rfl fun j hj => by rw [update_of_ne (show j≠i from fun h => hs (h ▸ hj))] : ∑ j∈s, _ = ∑ j∈s,divZ j p*g j p),
      ← Y p hp, Function.comp_apply,Function.comp_apply, show staged (insert i s) p=evalSmall i (staged s p) by
        ext1 j; by_cases h : j=i <;> simp [staged,evalSmall, *]]
    unfold evalSmall; ring

lemma layers (α : Type) [Fintype α] [DecidableEq α] (n : ℕ) (hs : 0<σ) :
    ∃ η K, 0<η ∧ η≤σ ∧ 0≤K ∧ ∀ (A : ℝ), 0 ≤ A → ∀ f : Phase α→ℂ, Firm σ A f → Rays n (f ∘ axes) →
      ∃ g : (Fin n → α) → Phase α→ℂ, (∀ b, Firm η (A*K) (g b)) ∧
        ∀ p∈strip η, f p = ∑ b : Fin n→α, (∏ i, divZ (b i) p)*g b p := by
  induction n generalizing σ with
  | zero => exact ⟨σ,1,hs,le_rfl,zero_le_one,fun A ha f hf hp => ⟨fun _ => f, fun b => by simpa using hf,by simp⟩⟩
  | succ n ih =>
    obtain ⟨τ,K,hτ,he,hK,H⟩ := ih (by positivity : 0 < σ/4)
    have hu : 0 ≤ priceDivision α σ := (priceDivision_pos σ hs _).le
    refine ⟨τ,priceDivision α σ*K,hτ,he.trans (by linarith),mul_nonneg hu hK,fun A hA f hf hx => ?_⟩
    obtain ⟨g,hg,hy⟩ := sustain hs hA univ f hf hx
    choose G hG hP using fun i => H _ (mul_nonneg hA hu) _ (hg i).1 (hg i).2
    rw [← mul_assoc]; refine ⟨fun b => G (b 0) (Fin.tail b), fun a => hG _ _,fun p hp => ?_⟩
    have hz : f 0=0 := by
      have hh := (rays_at_zero (hf.analytic_real 0)).1 (hx.weaker (by omega : 1 ≤ n+1)); simpa using hh
    have h := hy p (fun i => (hp i).trans_le he)
    rw [show staged Finset.univ p=0 from funext fun _ => if_pos (mem_univ _),hz,sub_zero] at h
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => α)),Fintype.sum_prod_type]
    simp_rw [h,hP _ p hp,Finset.mul_sum]; apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _; rw [Fin.prod_univ_succ, show (Fin.consEquiv (fun _ : Fin (n+1) => α)) (i,j) = Fin.cons i j from rfl]; simp [mul_assoc]

lemma transfers (n t : ℕ) (hs : 0<σ) : ∃ η K, 0<η ∧ η≤σ ∧ 0≤K ∧ ∀ A : ℝ, 0≤A →
    ∀ f : Space t→ℂ, Firm σ A f → Rays n (f ∘ axes) →
      ∃ g : (Fin n→Keys t) → Shift (Keys t) → ℂ, (∀ b, Width η (A*K) (g b)) ∧
      ∀ p∈strip η, f p=∑ y : Fin n→Keys t,(∏ j,q (plotted p ((y j).1.succ)) (y j).2)* Laurent.read (g y) p := by
  obtain ⟨τ,K,hτ,he,hK,H⟩ := layers (Keys t) n hs
  let η := τ/4
  let Z := (2*((1+η)/η))^(Fintype.card (Keys t))
  have hη : 0<η := by unfold η; positivity
  have hx : 2*η < τ := by unfold η; linarith
  refine ⟨η,K*Z,hη,by linarith,mul_nonneg hK (by unfold Z; positivity),fun A hA f hf hp => ?_⟩
  obtain ⟨g,hg,hv⟩ := H A hA f hf hp
  rw [← mul_assoc]; refine ⟨(fun y => Laurent.market (g y) 0), fun i => (hg i).1.issues (hg i).2 η η hη.le hη (by linarith),fun p hp => ?_⟩
  have hu : p∈ strip τ := fun i => (hp i).trans (by linarith)
  rw [hv p hu]; apply sum_congr rfl; intro i _
  rw [(hg i).1.paints (hg i).2 p hu]; congr 1

-- two directions, divide n on second leg, push s to first with phase π.
lemma twister (p : Momentum) (a : Axis) : Exterior.q p a = -mode p (step a)*Exterior.q (-p) a := by
  simp only [Exterior.q,Pi.neg_apply, factor, mul_neg, Complex.exp_neg]
  field_simp; ring

lemma twin_layers (n : ℕ) (r : Fin n→Fin 2) (hs : 0<σ) :
    ∃ η K, 0<η ∧ η≤σ ∧ 0≤K ∧ ∀ (A : ℝ), 0 ≤ A →
    ∀ f : Space 1→ℂ, Firm σ A f → Rays n (f ∘ axes) →
      ∃ g : (Fin n→Keys 1) → Shift (Keys 1)→ℂ,
        (∀ b, Width η (A*K) (g b)) ∧ ∀ p∈strip η, f p=∑ y : Fin n→Keys 1,(∏ j,q (plotted p (r j)) (y j).2) * Laurent.read (g y) p := by
  obtain ⟨w,C,hw,he,hC,H⟩ := transfers n 1 hs
  let η := w/4
  have ha : 0 < η := by unfold η; positivity
  let Z := (2*((1+η)/η))^(Fintype.card (Keys 1))
  have hc : 2*η < w := by unfold η; linarith
  refine ⟨η,C*Real.exp w^n*Z,ha,by linarith,by unfold Z; positivity,fun A hp f hf hx => ?_⟩
  obtain ⟨g,hg,hV⟩ := H A hp f hf hx
  let T (y : Fin n→Keys 1) (j : Fin n) (p : Space 1) :=
    if r j=0 then -mode (axisPair p) (step (y j).2) else 1
  let X y p := (∏ j,T y j p)*Laurent.read (g y) p
  have hb y : Firm w ((Real.exp w)^n*(A*C)) (X y) := by
    have he (j) : Firm w (Real.exp w) (T y j) := by
      unfold T; split
      · apply Firm.neg
        have hp : Laurent.size (step (y j).2:Cover)=1 := by
          unfold Laurent.size; rw [sum_eq_single (y j).2]; all_goals simp_all
        have h := Firm.mode (step (y j).2:Cover) hw; rw [hp] at h
        simpa only [Nat.cast_one,mul_one] using (pair_firm h)
      apply (Firm.const hw _).mono hw le_rfl; simp [Real.one_le_exp hw.le]
    apply Firm.mul _ (Firm.of_series (hg _) hw)
    have hu := firmProd univ _ _ hw (fun i _ => he i); simpa using hu
  have HE : A*(C*Real.exp w^n*Z)=(Real.exp w^n*(A*C))*Z := by ring
  rw [HE]; refine ⟨fun y => Laurent.market (X y) 0,fun y => (hb y).1.issues (hb y).2 η η ha.le ha (by linarith),fun p hp => ?_⟩
  have hu : p∈ strip w := fun i => (hp i).trans (by linarith)
  rw [hV p hu]; apply sum_congr rfl; intro b _
  rw [(hb b).1.paints (hb b).2 p hu]
  unfold X; rw [← mul_assoc,← prod_mul_distrib]
  congr 1; apply prod_congr rfl; intro i _
  unfold T; rw [show (b i).1=0 from Subsingleton.elim ..]
  have hs (p : Space 1) : plotted p 0 = -(axisPair p) := by simp [plotted,missing]; rfl
  split; next H => rw [H,hs,mul_comm]; exact twister (axisPair p) _
  next h => rw [show r i=1 by omega,mul_one]; rfl
end YM.Stationary
end

/-!
# True-grid scalar vertices after spending soft derivatives in position.
Orders in lists may repeat a slot. Domain unrestricted periods even ν=1;
complex profile `scrap` (incl imaginary coarse p) of fine data.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics
open scoped Topology ContDiff BigOperators
variable {α β : Type} [Fintype α] [DecidableEq α] {t n : ℕ} {c f m L : Side} {p : Momentum} {σ C : ℝ}

section phase

def sparksZ (p : Momentum) (l : List Axis) := (l.map (Exterior.q p)).prod
@[simp] lemma sparksZ_cons (q : Momentum) (i : Axis) (l) : sparksZ q (i::l)=Exterior.q q i*sparksZ q l := rfl

def darts (i : Axis) : Phase (Co m α)→ₗ[ℂ] Phase (Co m α) := LinearMap.pi (fun j=> LinearMap.proj (j.1+step i,j.2))-LinearMap.id
def swingD : List Axis → Phase (Co m α)→ₗ[ℂ] Phase (Co m α)
  | [] => LinearMap.id
  | i::l => darts i ∘ₗ swingD l
lemma tune_punch (k : Site m) (v : Phase α) (i : Axis) : darts i (tune k v)=Exterior.q (mon k) i • tune k v := by
  ext1 j
  change tune k v (j.1+step i,j.2)-tune k v j=_*_
  unfold tune Exterior.q; rw [cell_add, ← factor, ← wrap_step (n:=m),cell_wrap]; ring
lemma tune_blitz (k : Site m) (v : Phase α) (l) : swingD l (tune k v)=sparksZ (mon k) l • tune k v := by
  induction l with
  | nil => simp [swingD,sparksZ]
  | cons i l ih => rw [swingD,LinearMap.comp_apply, ih,map_smul,tune_punch, smul_smul, mul_comm]; rfl

def twitches (p : Momentum) (x : Cover) : Phase (Co L α)→ₗ[ℂ] Phase (Co L α) where
  toFun v j := scrap p v (lift j.1+x) j.2
  map_add' u v := by ext1 i; unfold scrap; simp [_root_.mul_add]
  map_smul' a v := by ext1 i; unfold scrap; simp [mul_left_comm]
def flick (p : Momentum) (i : Axis) : Phase (Co L α)→ₗ[ℂ] Phase (Co L α) := twitches p (step i)-LinearMap.id
def flight (p : Momentum) : List Axis→Phase (Co L α)→ₗ[ℂ] Phase (Co L α)
  | []=> LinearMap.id
  | i::l=> flick p i ∘ₗ flight p l
lemma twitches_scrap (v : Phase (Co L α)) (x r : Cover) (i) : scrap p (twitches p x v) r i=scrap p v (r+x) i := by
  change mode p (rent L r)*scrap p v (lift (wrap L r)+x) i = _; rw [show r+x=(lift (wrap L r)+x)+L.val • rent L r by rw [add_right_comm,← rent_balance],scrap_bank,mul_comm]
lemma flick_scrap (v : Phase (Co L α)) (i : Axis) r j : scrap p (flick p i v) r j=scrap p v (r+step i) j - scrap p v r j := by
  rw [← twitches_scrap, scrap, flick,LinearMap.sub_apply,Pi.sub_apply, _root_.mul_sub]; rfl
lemma flight_reset {r : Momentum} (h : rolls p r) (l : List Axis) : flight p l=(flight r l : Phase (Co L α)→ₗ[ℂ] Phase (Co L α)) := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [flight,ih,flight]; unfold flick; rw [show twitches p (step i)=(twitches r _ : Phase (Co L α)→ₗ[ℂ] Phase (Co L α)) by ext v j; exact scrap_reset h _ _ _]
lemma twitch_tiled (p : Momentum) (l : Site L) (v : Phase α) (r : Cover) : twitches p r (tiled p l v)=mode (aliasAt p l) r • tiled p l v := by
  funext i
  change scrap p (tiled p l v) _ _ = _; rw [scrap_tiled,mode_shift]; unfold tiled; exact mul_right_comm _ _ _ |>.trans (by simp [mul_comm,mul_left_comm])
lemma flick_tapes (p : Momentum) (l : Site L) (v : Phase α) (i : Axis) : flick p i (tiled p l v)=Exterior.q (aliasAt p l) i • tiled p l v := by
  rw [flick,LinearMap.sub_apply,LinearMap.id_apply,twitch_tiled,factor,Exterior.q,_root_.sub_smul,one_smul]

lemma flight_price (g : Ratio c f) (k : Site c) {p : Momentum} (h : rolls (mon k) p) (v : Phase (Co g.count α)) (l) (i : Site c) (x : Cover) (j) :
    swingD l (poured g k v) (wrap f x+g.embed i,j) = cell k i * scrap p (flight p l v) x j := by
  induction l generalizing x with
  | nil => exact scrap_pour g k i p h v x j
  | cons a l ih => change swingD l (poured g k v) (wrap f x+g.embed i+step a,j) - _ = cell k i*scrap p (flick p a (flight p l v)) x j
                   rw [flick_scrap,_root_.mul_sub, ← ih x, ← ih, map_add, wrap_step, LinearMap.id_apply, add_right_comm _ (g.embed i)]
end phase
end YM.Stationary
end

/-! # Unweighted network on physical scalar vertices. Uses actual budgets of
   the factorizations to identify coefficients. Subsequent pricing on strip. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics
open scoped Topology ContDiff BigOperators
variable {α ι G' : Type} [Fintype α] [DecidableEq α] {G : Gauge} {t n : ℕ} {c f m L : Side} {p : Momentum} {σ C : ℝ}

-- useful exchange when absolute summability proven pointwise, equality of
-- Record not a norm comparison.
def flyRec (F : ι → RecordM ℂ (Fin n) α) : RecordM ℂ (Fin n) α := recording fun i => ∑' j,F j (fun k => Pi.single (i k) 1)
lemma flyRec_recites (F : ι → RecordM ℂ (Fin n) α) (h : ∀ v : Fin n→Phase α,Summable (fun i => F i v))
    (v : Fin n → Phase α) : flyRec F v = ∑' j,F j v := by
  rw [flyRec,recording_apply]; simp_rw [← tsum_mul_left]; rw [← Summable.tsum_finsetSum (fun i _ => (h _).mul_left _)]
  exact tsum_congr fun i => (recording_apply _ _).symm.trans (expand_coord (F i) v)

lemma cell_prod_hymn (p : Fin n→Site m) (x : Site m) : ∏ j,cell (p j) x=cell (∑ i,p i) x := by
  symm; suffices hh : ∀ s : Finset (Fin n), cell (∑ j∈s,p j) x = ∏ j∈s,cell (p j) x from hh univ
  intro s; induction s using Finset.induction with
  | empty => simp [cell_duality _ x]
  | insert i s h IH => rw [sum_insert h,prod_insert h,cell_duality _ x,cell_add,cell_duality x,cell_duality x,IH]
lemma sparks_roll {r : Momentum} (h : rolls p r) (l) : sparksZ p l=sparksZ r l := by
  have he : Exterior.q p=Exterior.q r := by ext1 i; rw [Exterior.q,Exterior.q,← factor,← factor,h.exp]
  rw [sparksZ,he]; rfl

section k
abbrev Tailor (t : ℕ) := Shift (Keys t)
def legLane (x : Tailor t) : Fin (t+1) → Cover := Fin.cons 0 (fun i j=> x (i,j))
lemma gangRay (p : Fin (t+1)→ Site m) (x : Tailor t) : mode (outphase p) x=∏ j,cell (p j) (wrap m (legLane x j)) := by
    simp only [cell_wrap,legLane,Fin.prod_univ_succ,Fin.cons_zero,mode_zero,one_mul,Fin.cons_succ]
    unfold mode; rw [Fintype.sum_prod_type, Finset.mul_sum, Complex.exp_sum]; rfl
abbrev Stitch (t : ℕ) := Fin (t+1) → List Axis
abbrev Breed (t : ℕ) (α : Type) := Fin (t+1) → α

def factorRay (l : Stitch t) (k : Tailor t → ℂ) (p : Space t) := (∏ j,sparksZ (plotted p j) (l j))*Laurent.read k p
variable (l : Stitch t) (k : Tailor t→ℂ) (b : Breed t α)

def pinion (z : Tailor t) (x : Site m) : RecordM ℂ (Fin (t+1)) (Co m α) :=
    (MultilinearMap.mkPiRing ℂ (Fin (t+1)) (k z)).compLinearMap (fun j => LinearMap.proj (x+wrap m (legLane z j),b j) ∘ₗ swingD (l j))
lemma pinion_eval (z : Tailor t) (x : Site m) (v : Fin (t+1)→Phase (Co m α)) : pinion l k b z x v=(∏ i,swingD (l i) (v i) (x+wrap m (legLane z i),b i))*k z := rfl

def pinRing (m : Side) : RecordM ℂ (Fin (t+1)) (Co m α) := flyRec fun z => ∑ i,pinion l k b z i
lemma pinRing_reach (he : Width σ C k) (hw : 0≤σ) (x : Site m) (v : Fin (t+1)→Phase (Co m α)) : Summable fun i => pinion l k b i x v := by
  have hh := he.summable hw
  let V j := ‖swingD (l j) (v j)‖
  refine Summable.of_norm_bounded (hh.norm.mul_left (∏ i,V i)) fun i => ?_
  rw [pinion_eval,norm_mul]; simp_rw [norm_prod]; gcongr; exact norm_le_pi_norm _ _
lemma pinRing_on (he : Width σ C k) (hw : 0≤σ) (v : Fin (t+1)→Phase (Co m α)) :
    pinRing l k b m v = ∑' z,∑ x : Site m,pinion l k b z x v := by
  have hv v : Summable (fun z => (∑ i : Site m,pinion l k b z i) v) := by simp_rw [_root_.sum_apply]; exact summable_sum fun i _ => pinRing_reach l k b he hw i v
  rw [pinRing,flyRec_recites _ hv]; simp only [_root_.sum_apply]

lemma pinRing_rec (he : Width σ C k) (hw : 0≤σ) (p : Fin (t+1)→ Site m) (a : Breed t α) :
    pinRing l k b m (fun i => relay (p i) (a i))= if b=a ∧ ∑ i,p i=0 then
      (Fintype.card (Site m):ℂ)*factorRay l k (outphase p) else 0 := by
  rw [pinRing_on _ _ _ he hw]
  let u (x : Tailor t) (j : Fin (t+1)) := sparksZ (mon (p j)) (l j) * cell (p j) (wrap m (legLane x j))*((Pi.single (a j) 1:Phase α) (b j))
  have hv (x : Tailor t) (z : Site m) : pinion l k b x z (fun i=>relay (p i) (a i))=cell (∑ i,p i) z * ((∏ i,u x i)*k x) := by
    rw [pinion_eval]; simp only [relay,tune_blitz,Pi.smul_apply,tune,smul_eq_mul]; rw [← _root_.mul_assoc, ← cell_prod_hymn,← Finset.prod_mul_distrib]; congr 1; apply prod_congr rfl; intro i _
    unfold u; rw [cell_add]; ring
  simp_rw [hv,← Finset.sum_mul]
  split
  next hz => obtain ⟨rfl,hz⟩ := hz; simp_rw [hz]; unfold factorRay Laurent.read; rw [_root_.mul_left_comm, ← tsum_mul_left, ← tsum_mul_left]
             refine tsum_congr fun i => ?_
             rw [gangRay]
             have hv j : sparksZ (plotted (outphase p) j) (l j)=sparksZ (mon (p j)) (l j) := sparks_roll (ties hz j) _
             simp_rw [hv]; simp [cell,u,prod_mul_distrib]; ring
  next h => refine Eq.trans (tsum_congr (g:=fun _ => 0) ?_) tsum_zero; intro z; by_cases hp : ∑ i,p i=0
            · have he : ∃ i,a i ≠ b i := by by_contra! hy; exact h ⟨(funext hy).symm,hp⟩
              obtain ⟨i,hi⟩ := he
              rw [prod_eq_zero (i:=i) (mem_univ i) (by simp [u,hi,Ne.symm hi]),zero_mul,mul_zero]
            rw [sum_cell hp, zero_mul]
end k
end YM.Stationary
end
