import YM.Next.STATIONARY.Films.Frame


set_option autoImplicit false
/-!
# Actual widths of crossings from stipulated kernels.
 This gate DOES NOT follow from stationary alone; includes all rows per
 residue and few actual derivatives. Forecast sign checked at fold boundary. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {α β : Type} {t n : ℕ} {c f m L : Side} {p : Momentum} {σ C A : ℝ}
-- readin for generics
lemma earn_delta (L : Side) (hl : Odd L.val) (a : Site L) (i : Axis) :
    rent L (lift a+step i) = if lift a i=((L.val/2:ℕ):ℤ) then step i else 0 := by
  have hh : 0 < L.val := L.pos
  obtain ⟨k,hk⟩ := hl
  symm; split
  next he =>
    have h : lift (wrap L (lift a+step i))=lift a+step i - L.val • step i := by
      apply lift_eq_iff.mpr
      refine ⟨by rw [map_sub,map_nsmul,show L.val • wrap L (step i) = 0 from ?_,sub_zero]
                 funext j; rw [Pi.smul_apply, nsmul_eq_mul]; simp [Per], fun j => ?_⟩
      have hx := lift_centers a j; by_cases hy : j=i <;> simp only [Pi.sub_apply,Pi.add_apply, step_apply,nsmul_eq_mul] <;> simp [hy] <;> omega
    apply rent_unique; rw [h]; abel
  next he =>
    apply rent_unique; rw [smul_zero, add_zero]; symm; apply lift_eq_iff.mpr
    refine ⟨rfl,fun j => ?_⟩
    have hx := lift_centers a j; by_cases hy : j=i <;> simp only [Pi.add_apply,step_apply] <;> simp [hy]; · rw [hy] at hx; omega
    exact hx
lemma discounted_read (F : Cross L α β) (h : F.strip σ C) (hl : Odd L.val) (a : Site L) (i j) (r : Axis) (hw : p∈strip σ) :
    (forwardC L F r).read p (a,i) j=mode p (rent L (lift a+step r))*F.read p (wrap L (lift a+step r),i) j-F.read p (a,i) j := by
  let d := rent L (lift a+step r)
  let z := wrap L (lift a+step r)
  have hz : z=a+step r := by unfold z; simp
  have hv b : forwardC L F r (a,i) j b= F (z,i) j (b-d)-F (a,i) j b := by rw [hz, forwardC,show d=_ from earn_delta L hl a r]
  unfold Row.read Laurent.read; simp only [of_apply, hv, smul_eq_mul,Complex.ofReal_sub,_root_.mul_sub]
  have ht x j : Summable (fun v => mode p v * (F x j v:ℂ)) := ((F.constant_strip h x j).series p (fun i=>(hw i).le)).2.1.of_norm
  have hh : (fun v => mode p v * (F (z,i) j (v-d):ℂ))∘ (Equiv.addRight d)=(fun v => mode p d * (mode p v*(F (z,i) j v:ℂ))) := by funext b; simp only [Function.comp_apply,show Equiv.addRight d b = b+d from rfl,add_sub_cancel_right,mode_shift]; ring
  have he : Summable (fun v => mode p v * (F (z,i) j (v-d):ℂ)) := by apply (Equiv.summable_iff (Equiv.addRight d)).mp; rw [hh]; exact (ht _ j).mul_left _
  rw [he.tsum_sub (ht (a,i) j)]
  congr 1; rw [← Equiv.tsum_eq (Equiv.addRight d)]; change tsum ((fun v => mode p v * (F (z,i) j (v-d):ℂ))∘_) = mode p d * _; rw [hh,tsum_mul_left]

section prof
abbrev LocalCross (P : Patch) := Cross P.L (TypeFace 1) (TypeFace 1)
def moonlit (G : Gauge) (P : Patch) (F : LocalCross P) : Bridge G P := fun p=> Matrix.of fun i j => if i.2.2=j.2 then F.read p (i.1,i.2.1) j.1 else 0
variable (G) (F : LocalCross P)
lemma moon_stamp
    (v : Loc G 1) (r : Axis) (h : F.strip σ C) (hw : p∈strip σ) :
    moonlit G P (forwardC P.L F r) p *ᵥ Pi.single v 1 = flick p r (moonlit G P F p *ᵥ Pi.single v 1) := by
  ext1 a; simp only [mulVec_single]; unfold moonlit
  simp only [flick,LinearMap.sub_apply,Pi.sub_apply]; unfold twitches scrap; simp
  split_ifs; · simpa using discounted_read F h P.odd_side a.1 a.2.1 v.1 r hw
  rw [sub_zero]
lemma moon_flag (h : F.strip σ C) (hs : 0<σ) : Poster σ (moonlit G P F) := by
  refine ⟨fun he a b => ?_,fun hp h => ?_⟩
  · unfold moonlit; simp only [Matrix.of_apply]; split
    exact (Firm.of_series (F.constant_strip h _ _) hs).1.hol _ he
    exact differentiableAt_const _
  ext i j; unfold moonlit; simp only [of_apply]; obtain ⟨z,rfl⟩ := hp; rw [F.periods]

lemma moon_aim (h : F.strip σ C) (hs : 0<σ) (hp : 0≤C) (hw : p∈strip σ) (v : Loc G 1) (i) :
    ‖(moonlit G P F p*ᵥ Pi.single v 1) i‖≤C := by
  change ‖(moonlit G P F p*ᵥ Pi.single _ _) i‖ ≤ _; rw [mulVec_single]
  change ‖((moonlit G P F p) i v:ℂ)*1‖ ≤ _
  rw [mul_one]; simp only [moonlit,Matrix.of_apply]; split
  exact (Firm.of_series (F.constant_strip h _ _) hs).2 _ hw
  simpa
end prof
end YM.Stationary
end

/-! # Producer rectifications. Keep forecasts widths and stellar pre-L. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {α β : Type} {n : ℕ} {c f m L : Side} {p : Momentum} {σ η C A : ℝ}
-- weighted crossings

def Headers (F : LocalCross P) (n : ℕ) (σ C : ℝ) := ∀ l : List Axis, l.length≤n → (advanceC P.L F l).strip σ (C/(P.L.val:ℝ)^(1+l.length))
def Cruise (K : Bridge G P) (n : ℕ) (σ C : ℝ) := Poster σ K ∧ 0≤ C ∧ ∀ l : List Axis, l.length≤n → ∀ p∈strip σ,∀ i a,
    ‖flight p l (K p *ᵥ Pi.single i 1) a‖ ≤ inch P.L^(1+l.length)*C

lemma Cruise.less {K : Bridge G P} (h : Cruise K n σ C) (ht : η≤σ) : Cruise K n η C := ⟨⟨fun p => h.1.shape (fun i => (p i).trans_le ht),fun hp hv=>h.1.shifts hp (fun i=>(hv i).trans_le ht)⟩,h.2.1,fun i hi p hp => h.2.2 i hi p (fun j=> (hp j).trans_le ht)⟩
lemma Headers.cruise (G : Gauge) {F : LocalCross P} (h : Headers F n σ C) (hs : 0<σ) (hp : 0≤C) : Cruise (moonlit G P F) n σ C := by
  refine ⟨moon_flag G F (h [] (Nat.zero_le _)) hs,hp,fun l he p ht v b => ?_⟩
  have hx : moonlit G P (advanceC P.L F l) p *ᵥ Pi.single v 1=flight p l (moonlit G P F p*ᵥ Pi.single v 1) := by
    induction l with
    | nil => rfl
    | cons i l IH => rw [advanceC,moon_stamp _ _ _ _ (h l (by simp at he; omega)) ht, IH (by simp at he; omega)]; rfl
  rw [← hx,(show inch P.L^(1+l.length)*C=C/(P.L.val:ℝ)^(1+l.length) by unfold inch; rw [inv_pow,mul_comm,← div_eq_mul_inv])]; exact moon_aim G (advanceC P.L F l) (h _ he) hs (by positivity) ht _ _

def cabinTicket (G : Gauge) (C : ℝ) := Real.sqrt (Fintype.card (Loc G 1))* C+Real.exp 4
lemma cabin_paid (G : Gauge) (hc : 0≤C) : Real.exp 4≤ cabinTicket G C := le_add_of_nonneg_left (mul_nonneg (Real.sqrt_nonneg _) hc)

lemma Cruise.stars {Φ : Bridge G P} (h : Cruise Φ n σ C) (hp : σ≤1) : Spotlight P (arriving Φ) σ (cabinTicket G C) := by
  refine spotlight_cape (fun p hc v i=> ?_) (cabin_paid G h.2.1) h.1 hp
  let u := (Φ p*ᵥ Pi.single v 1)
  let f j:= u (i,j)
  have hx j : ‖f j‖ ≤ inch P.L*C := by simpa only [flight,LinearMap.id_apply,List.length_nil,add_zero,pow_one] using h.2.2 [] (Nat.zero_le _) p hc v (i,j)
  have hC := h.2.1
  have hA := inch_pos P.L
  change slug (stackSlice i u)≤ _
  have ht : slug (stackSlice i u) ≤ Real.sqrt (Fintype.card (Loc G 1))*(inch P.L*C) := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [slug_sq,mul_pow,Real.sq_sqrt (by positivity),show ↑(Fintype.card (Loc G 1))* (inch P.L*C)^2= ∑ _ : Loc G 1,(inch P.L*C)^2 by simp]
    exact sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hx _) _
  exact ht.trans (by unfold cabinTicket; nlinarith only [Real.exp_pos 4,hA])

section bound
variable (S : StepData c f) {F : LocalCross S.patch}

lemma launchBridge (G : Gauge) (h : F.safe) : Premise S (installed S.ratio F) (moonlit G S.patch F) := by
  let L:= S.patch.L
  let g:= S.ratio
  let P:= installed g F
  let e := unitSplit G S 1
  intro p q he v
  rw [add_zero]
  ext1 x
  rcases x with ⟨y,b,j⟩
  let i := g.assemble (y,b)
  have hx : e (i,j)=(y,b,j) := by change splitCo g _ (i,j)=_; rw [split_co]; simp [i]
  let w := tune p v
  let M := uniformM (G:=G) P
  have hb (n l) : moonlit G S.patch F q (b,n) l= _ := (rfl : _ = if n.2=l.2 then F.read q (b,n.1) l.1 else 0)
  have hr : (moonlit G S.patch F q*ᵥ v) (b,j)=(F.read q*ᵥ pick v j.2) (b,j.1) := by
    unfold Matrix.mulVec dotProduct; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro l _; simp_rw [hb,ite_mul]; simp [pick]
  have ht : (approached P *ᵥ tune p (pick v j.2)) (i,j.1) = cell p y*(F.read q *ᵥ pick v j.2) (b,j.1) := by
    let K := F.acts c
    calc
      _ = (approached K *ᵥ tune p (pick v j.2)) (splitCo g _ (i,j.1)) := rfl
      _ = _ := by rw [Jaunt.row F h _ _ he, add_zero, split_co]; simp [tune,i]; rfl
  have hh : (approached (patron G P)*ᵥ w) (i,j)=_ := (congr_fun (patron_contract P w j.2) (i,j.1)) |>.trans ht
  change (approached (repackM e (Equiv.refl _) (patron G P))*ᵥ w) (y,b,j)=cell p y* (moonlit G S.patch F q *ᵥ v) (b,j); rw [hr,← hh]; unfold Matrix.mulVec dotProduct
  apply sum_congr rfl; intro a _
  simp only [repackM,approached, Matrix.map_apply,Matrix.submatrix_apply, ← hx,e.symm_apply_apply]; rfl
end bound
end YM.Stationary
end

/-!
# Left perturbation of fine input. For the *actual* flare calculation
and for infrared leading vertices. `sortie` inserts tag false baseline,
true perturbation. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {P : Patch} {α β R : Type} [Fintype α] [DecidableEq α] [CommRing R] {n : ℕ} {c f m L : Side} {p : Momentum} {σ C A : ℝ}

abbrev Crisp (G : Gauge) := Bool × Loc G 1

def wheat (b : Bool) : (Co m (Bool × α)→R) →ₗ[R] (Co m α → R) := LinearMap.pi fun i => LinearMap.proj (i.1,b,i.2)
def spout (b : Bool) : (α→R) →ₗ[R] (Bool × α → R) := LinearMap.pi fun i=>(if i.1=b then LinearMap.proj i.2 else 0)
def sprout (b : Bool) : (Co m α→R) →ₗ[R] (Co m (Bool × α)→ R) := LinearMap.pi fun i=> if i.2.1=b then LinearMap.proj (i.1,i.2.2) else 0

@[simp] lemma wheat_swims (b : Bool) (v : Co m α → R) : wheat b (sprout b v)=v := by ext1 i; simp [wheat,sprout]
lemma wheat_avoids {a b} (h : a ≠ b) (v : Co m α → R) : wheat a (sprout b v)=0 := by ext1 i; simp [wheat,sprout,h]
lemma sprout_forward (v : Phase α) (b) (p : Site m) : sprout b (tune p v) = tune p (spout b v) := by ext1 i; rcases i with ⟨i,j,k⟩; by_cases H:j=b <;> simp [spout,sprout,tune,H]
lemma sprout_axes b (v : Corn (Co m α)) : sprout b (axes v)=axes (sprout b v) := by
  ext1 a; rcases a with ⟨a,i,y⟩; by_cases H:i=b <;> simp [axes,sprout,H]

section fine

variable (G) (m)
-- movement params chart Xi; including >1 derivatives

def dough (x : Corn (Co m (Crisp G))) := content (input G m (wheat true x)* input G m (wheat false x))
@[simp] lemma dough_zero : dough G m 0=0 := by simp [dough]

def oven (x : Corn (Crisp G)) (i : Axis) (b : Bool) : G.Color := WithLp.toLp 2 (fun j=> x (b,coord i,j))
def acorn (i : Loc G 1) (x : Corn (Crisp G)) := G.plog (G.mat (G.lieExp (oven G x (axisEquiv.symm i.1) true)* G.lieExp (oven G x (axisEquiv.symm i.1) false))) i.2

lemma acorn_reads (x : Corn (Co m (Crisp G))) (a : Lines G m 1) :
    dough G m x a= acorn G a.2 (fun i=>x (a.1,i)) := by
  rcases a with ⟨a,i,b⟩; obtain ⟨k,rfl⟩ := axisEquiv.surjective i
  change dough G m x (a,(coord k,b))=acorn G (coord k,b) _
  unfold acorn; simp only [show axisEquiv.symm (coord k)=k from axisEquiv.symm_apply_apply _]
  rw [← arm_apply G m 1 (dough G m x)]; unfold dough; rw [content_at,Pi.mul_apply,encode_link,encode_link]; rfl
lemma dough_floats : AnalyticAt ℝ (dough G m) 0 := by
  let h (b : Bool) : Corn (Co m (Crisp G)) →L[ℝ] Link G m := (wheat b).toContinuousLinearMap
  apply content_analytic (F:=fun i => input G m (h true i) * input G m (h false i)) (by simp only [map_zero,input_zero, mul_one])
  rintro ⟨i,j⟩; simp_rw [Pi.mul_apply, G.mat_mul, encode_link]
  apply ContDiffAt.analyticAt; apply ContDiffAt.mul <;> apply G.exp_jet.contDiffAt.comp <;> fun_prop
lemma acorn_green (i : Loc G 1) : AnalyticAt ℝ (acorn G i) 0 := by
  let a : Co 1 (Loc G 1):=(0,i)
  let h : Corn (Crisp G) →L[ℝ] Corn (Co 1 (Crisp G)) := (LinearMap.pi (fun i : Co 1 (Crisp G) => LinearMap.proj i.2)).toContinuousLinearMap
  have hp x : acorn G i x=dough G 1 (h x) a := (acorn_reads G 1 (h x) a).symm
  rw [funext hp]; let z : Corn (Co 1 (Crisp G)):=0
  have he : AnalyticAt ℝ (fun x => dough G 1 x a) z := (contDiffAt_pi.mp ((dough_floats G 1).contDiffAt (n:=ω)) a).analyticAt
  exact AnalyticAt.comp (g:=fun x => dough G 1 x a) (f:=h) (show AnalyticAt ℝ _ (h 0) from (map_zero h) ▸ he) (h.analyticAt _)

lemma dough_signal (n : ℕ) (p : Fin n→Site m) (V : Fin n→Phase (Crisp G)) :
    cluster (dough G m) 0 n (fun i=> tune (p i) (V i))=tune (∑ i,p i) (fun j=> beat (acorn G j) 0 n V) := by
  let s := fun (_ : Loc G 1) (i : Crisp G) => i
  have he a : (fun x=> dough G m x a)= acorn G a.2 ∘ consult (Crisp G) s (fun _ _=> 0) ℝ a := funext fun x => by
    rw [acorn_reads]; unfold consult; simp [s]; rfl
  have ht := summons (Crisp G) (acorn G) s (fun _ _ => 0) (dough G m) he (acorn_green G) p _ (fun i => rolls.refl (mon (p i))) V
  rw [ht]; congr 1; funext a; unfold bulletin; simp; rfl
end fine
end YM.Stationary
end

/-!
# Flavor left vertices. Placement rays coordinated, no fin propagation
 outside core draws. Base charges assembled separately. This formulation
also gives αInfra annulus extension. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {α β R : Type} [Fintype α] [DecidableEq α] [CommRing R] {n t u : ℕ} {c f m L : Side} {p : Momentum} {σ C A η : ℝ}

section malt
-- universal box compression

def calls (x : ℕ) (σ : ℝ) := σ/((x+1:ℝ)^2)

def juggleR (b : OrderedFinpartition (t+1)) (h : n+1=b.length) (p : Space t) : Space n := fun i=> tally b (plotted p) (Fin.cast h i.1.succ) i.2

lemma comedy_diff (b : OrderedFinpartition (t+1)) (h : n+1=b.length) : Differentiable ℂ (juggleR b h) := by
  refine differentiable_pi.mpr fun a => (differentiable_pi (Φ:=fun p => tally b (plotted p) (Fin.cast h a.1.succ))).mp (Differentiable.fun_sum (fun i _ => platform_diffs _)) _
lemma comedy_routes (b : OrderedFinpartition (t+1)) (h : n+1=b.length) (p : Space t) (x : Shift (Keys t)) : rolls (juggleR b h p) (juggleR b h (p+reciprocal x)) := by
  have he : rolls p (p+reciprocal x) := ⟨x,rfl⟩
  refine rolls_keys fun i=> ?_
  exact rolls_sums (fun j => projections_roll he (b.emb (Fin.cast h i.succ) j))
lemma comedy_strips (b : OrderedFinpartition (t+1)) (h : n+1=b.length) (hs : 0<σ) (p : Space t) (hp : p∈strip (calls (t+1) σ)) : juggleR b h p ∈ strip σ := by
  rintro ⟨i,j⟩; let r := calls (t+1) σ
  have hh : 0<r := by unfold r calls; positivity
  let a := Fin.cast h i.succ
  unfold juggleR tally; rw [Finset.sum_apply,Complex.im_sum]; refine lt_of_le_of_lt (Finset.abs_sum_le_sum_abs ..) ?_
  let M := (↑t+1 : ℝ)*r
  calc
    _ ≤ ∑ _ : Fin (b.partSize a), M := sum_le_sum fun k _ => (tilted p hp hh (b.emb a k) j).le
    _ ≤ ((↑t+1:ℝ))*M := by simp; gcongr; exact_mod_cast b.partSize_le a
    _ < σ := by
      unfold M r calls; push_cast; have ht : 0<(t:ℝ)+1+1 := by positivity
      field_simp; nlinarith only [hs,ht]
lemma comedy_firm (b : OrderedFinpartition (t+1)) (h : n+1=b.length) {F : Space n→ℂ} (hp : Firm σ C F) (hx : Rays u (F ∘ axes)) :
    Firm (calls (t+1) σ) C (F ∘ juggleR b h) ∧ Rays u (F ∘ juggleR b h ∘ axes) := by
  have hs := hp.width_pos
  refine ⟨hp.comp _ (comedy_diff _ _) (by unfold calls; positivity) (comedy_strips b h hs) (comedy_routes b h),?_⟩
  intro p
  choose x H ht using roots_q p
  let r : Corn (Keys n) := fun i=> (tally b x (Fin.cast h i.1.succ)) i.2
  refine (hx r).congr_left fun y => ?_; change F _=F _; congr 1; funext i; simp only [axes,r, juggleR,tally,ht,Pi.smul_apply,Finset.sum_apply, Function.comp_apply]; push_cast; simp [Finset.mul_sum]
end malt

lemma note_not_tone {v : Picture G t} {F : Link G m→ℝ} (p : Breed t (Site m)) (hp : ∑ i,p i ≠0) (h : Recorded v F 0) (U : Breed t (Phase (Loc G 1))) : beat F 0 _ (fun i => tune (p i) (U i))=0 := by
  let T i (j : Loc G 1) := U i j • relay (p i) j
  rw [show (fun i=> tune _ _)=(fun i=> ∑ j,T i j) by
    funext i x
    rw [Finset.sum_apply]; simp [T,tune,relay,Pi.single_apply,mul_comm],beat_as_cost F,_root_.smul_apply, MultilinearMap.map_sum, sum_eq_zero]
  · simp
  intro i _
  rw [show noteAt F _ _=_ from (noteAt F (t+1)).map_smul_univ (fun j=> U j (i j)) (fun j=> relay _ _)]
  change _*noteAt F (t+1) (glyph p (fun j=> (i j).2) (fun j=> (i j).1))=_
  rw [(record_exact ..).1 h,collected,if_neg hp,mul_zero]
end YM.Stationary
end

/-!
# Build the infrared vertices of `dough` in the (left,right) chart.
Strip shapes at exact mesh incl tilted rolls. The BEAT budget (rather
than note). Works at prescribed quotient soft order s.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {α β R : Type} [Fintype α] [DecidableEq α] [CommRing R] {n t u : ℕ} {c f m L : Side} {σ C A η : ℝ}

section oil
variable (v : Breed t Bool) (b : OrderedFinpartition (t+1))

def scroll (U : Link G m→ℝ) (p : Breed t (Site m)) (w : Breed t (Phase (Loc G 1))) :=
    beat U 0 b.length (fun i=> cluster (dough G m) 0 (b.partSize i) (fun j=>sprout (v (b.emb i j)) (tune (p (b.emb i j)) (w (b.emb i j)))))

def scrollStar (w : Breed t (Phase (Loc G 1))) (i : Fin b.length) : Phase (Loc G 1) := fun j =>
    beat (acorn G j) 0 (b.partSize i) (fun j=> spout (v (b.emb i j)) (w (b.emb i j)))
lemma star_scroll (U : Link G m→ℝ) (p : Breed t (Site m)) (w : Breed t (Phase (Loc G 1))) :
    scroll v b U p w=beat U 0 b.length (fun i => tune (tally b p i) (scrollStar v b w i)) := by unfold scroll; simp_rw [sprout_forward,dough_signal]; rfl

def liquid (v : Breed t Bool) (U : Link G m→ℝ) : RecordM ℂ (Fin (t+1)) (Lines G m 1) :=
    (beat (U ∘ dough G m) 0 _).compLinearMap (fun j=> sprout (v j))
lemma malt_bill_pick (U : Link G m→ℝ) (h : AnalyticAt ℝ U 0) (p : Breed t (Site m)) (w : Breed t (Phase (Loc G 1))) :
    liquid v U (fun i=> tune (p i) (w i))= ∑ b, scroll v b U p w := by
  rw [liquid,MultilinearMap.compLinearMap_apply,chain_eval (dough G m) U 0 (dough_floats G m) (dough_zero G m ▸ h),dough_zero]; rfl

def sip (h : n+1=b.length) (f : Picture G n) (w : Breed t (Phase (Loc G 1))) (p : Space t) :=
    ((n+1).factorial:ℂ)*recordField f (juggleR b h p) (scrollStar v b w ∘ Fin.cast h)
-- arbitrary real phases ext but tally with lifts.
lemma drink (h : n+1=b.length) (f : Picture G n) {U : Link G m→ℝ} (hx : Recorded f U 0) (he : ∀ i j,Firm σ A (f i j))
    (p : Breed t (Site m)) (w : Breed t (Phase (Loc G 1))) : scroll v b U p w=
      if ∑ i,p i=0 then (Fintype.card (Site m):ℂ)*sip v b h f w (outphase p) else 0 := by
  rcases b with ⟨l,d,H,z,h1,h2,h3,h4⟩; dsimp only at h; subst l; let c : OrderedFinpartition (t+1):=⟨_,d,H,z,h1,h2,h3,h4⟩
  let y := tally c p
  rw [star_scroll]; split
  next hp =>
    have hu (i : Fin (n+1)) : rolls (mon (y i)) (tally c (plotted (outphase p)) i) := collide (fun j=>p (c.emb i j)) _ (fun j=> (ties hp _).symm)
    have H := beat_recorded he hx y (tally c (plotted (outphase p))) ((c.sum_sigma_eq_sum p).trans hp) hu (scrollStar v c w)
    rw [cents] at H; push_cast at H
    exact H
  next hp =>
    have he : ∑ j,y j≠0 := by rw [show ∑ j,y j=∑ i,p i from c.sum_sigma_eq_sum p]; exact hp
    exact note_not_tone y he hx _

def drinkCost (w : Breed t (Phase (Loc G 1))) := (b.length.factorial:ℝ)*(∑ i : Fin b.length→Loc G 1, ‖∏ j, scrollStar v b w j (i j)‖)
lemma liquor (h : n+1=b.length) {f : Picture G n} (hx : ∀ i j,Firm σ A (f i j) ∧ Rays u (f i j ∘ axes)) (hs : 0<σ) (w : Breed t (Phase (Loc G 1))) :
    Firm (calls (t+1) σ) (A*drinkCost v b w) (sip v b h f w) ∧ Rays u (sip v b h f w ∘ axes) := by
  rcases b with ⟨l,d,H,z,h1,h2,h3,h4⟩; dsimp only at h; subst l; let b : OrderedFinpartition (t+1):=⟨_,d,H,z,h1,h2,h3,h4⟩
  let c := calls (t+1) σ
  let k (i : Fin (n+1)→Loc G 1) := ∏ j, scrollStar v b w j (i j)
  let M (i : Fin (n+1)→Loc G 1) (p : Space t) := f (fun j => (i j).2) (fun j => (i j).1) (juggleR b (Eq.refl (n+1)) p)
  have he (i : Fin b.length →Loc G 1) := comedy_firm (u:=u) b (Eq.refl (n+1)) (hx (fun j=> (i j : Loc G 1).2) (fun j=> (i j : Loc G 1).1)).1 (hx (fun j=> (i j : Loc G 1).2) (fun j=> (i j : Loc G 1).1)).2
  let y := ((n+1).factorial:ℂ)
  change Firm c (A*((n+1).factorial*∑ i,‖k i‖)) (fun p=>y*∑ i,k i*M i p) ∧ Rays u _
  have ht : 0 < c := by unfold c calls; positivity
  constructor
  · convert (Firm.const ht y).mul (Firm.sum Finset.univ (fun i p=> k i*M i p) (fun i => ‖k i‖*A) ht (fun i _ => (Firm.const ht (k i)).mul (he i).1)) using 1
    simp only [← sum_mul, y,Complex.norm_natCast]; ring
  intro a; refine IsBigO.const_mul_left ?_ y
  change (fun b' : ℝ => ∑ i,k i*M i (axes (b' • a)))=O[cutRay] _
  exact Asymptotics.IsBigO.sum fun i _ => ((he i).2 a).const_mul_left _
end oil
end YM.Stationary
end

/-!
# Coalescence powers for the perturbed path Hessian, no constants from L
other than ones funded earlier. Can attach cuts only in downstream anneal.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {t n u : ℕ} {m c f L : Side} {σ A C η : ℝ} {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α]

def Drinkable (k : ℕ) (m : ℕ→Side) (U : ∀ i,Link G (m i)→ℝ) (v : ℕ) (σ C : ℝ) := ∃ Q : Picture G k,
    (∀ i,Recorded Q (U i) 0) ∧ ∀ i j,Firm σ C (Q i j) ∧ Rays v (Q i j ∘ axes)
def DrinkIt (Q : Picture G t) (U : Link G m→ℝ) (h : Breed t Bool) := ∀ a b p, liquid h U (glyph p a b)=collected Q p a b

section sd
variable {v : Breed t Bool} {m : ℕ→Side} (U : ∀ i,Link G (m i)→ℝ) (b : OrderedFinpartition (t+1))
variable (h : ∀ n>0,n≤t → Drinkable n m U u σ A) (he : ∀ i, fderiv ℝ (U i) 0=0)

def paletteOne (a : Ink G (t+1)) (b : Run (t+1)) : Breed t (Phase (Loc G 1)) := fun i=> Pi.single (b i,a i) 1
include h he
lemma cuddles (hw : 0<σ) (hv : 0≤ A) (v : Breed t Bool) (w : Breed t (Phase (Loc G 1))) :
    ∃ k : Space t→ℂ,Firm (calls (t+1) σ) (A*|drinkCost v b w|) k ∧ Rays u (k ∘ axes) ∧ ∀ i (p : Breed t (Site (m i))),
      scroll v b (U i) p w=if ∑ j,p j=0 then (Fintype.card (Site (m i)):ℂ)*k (outphase p) else 0 := by
  have hx := b.length_pos (by omega); have hy := b.length_le
  have ht : 0<calls (t+1) σ := by unfold calls; positivity
  match hc : b.length with
  | 0 => omega
  | 1 =>
    refine ⟨fun _ =>0,(Firm.zero ht).mono ht le_rfl (by positivity),fun _ => isBigO_zero ..,fun i p => ?_⟩
    suffices h : iteratedFDeriv ℝ b.length (U i) 0=0 by unfold scroll beat; rw [h,enlarge]; split <;> simp [recording_apply]
    rw [hc]; ext1 x; simp [iteratedFDeriv_one_apply,he i]
  | n+2 =>
    obtain ⟨Q,hQ,H⟩ := h (n+1) (by omega) (by omega)
    have he := liquor v b hc.symm H hw w
    exact ⟨_,he.1.mono ht le_rfl (mul_le_mul_of_nonneg_left (le_abs_self _) hv),he.2,fun i => fun p=> drink v b _ Q (hQ i) (fun i j => (H i j).1) p w⟩
omit h he in
def pintCost (v : Breed t Bool) (G : Gauge) := ∑ a : Ink G (t+1), ∑ b : Run (t+1),∑ c,|drinkCost v c (paletteOne a b)|

theorem wedlock (v : Breed t Bool) (hp : ∀ i, AnalyticAt ℝ (U i) 0) (hs : 0<σ) (hC : 0≤ A) : ∃ Q : Picture G t, (∀ i, DrinkIt Q (U i) v) ∧
    ∀ i j,Firm (calls (t+1) σ) (A*pintCost v G) (Q i j) ∧ Rays u (Q i j ∘ axes) := by
  choose k hK hr hQ using fun c (i : Ink G (t+1)) j=> cuddles U c h he hs hC v (paletteOne i j)
  refine ⟨fun i j p=> ∑ c,k c i j p, fun i a b p => ?_,fun i j=> ⟨?_,fun x=> Asymptotics.IsBigO.sum fun r _ => hr r i j x⟩⟩
  · rw [show glyph p a b=(fun i=>tune (p i) (paletteOne a b i)) from rfl,malt_bill_pick _ _ (hp i)]
    unfold collected; simp_rw [hQ]; split <;> next hx => simp [*,mul_sum]
  have ht : 0<calls (t+1) σ := by unfold calls; positivity
  refine (Firm.sum _ _ _ ht (fun a _ => hK a i j)).mono ht le_rfl ?_
  rw [← mul_sum]; gcongr; exact (single_le_sum (s:=univ) (f:=fun b : Run (t+1) => ∑ c, |drinkCost v c (paletteOne i b)|) (fun i _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ j)).trans (single_le_sum (s:=univ) (f:=fun i : Ink G (t+1) => ∑ b : Run (t+1),∑ c,|drinkCost v c (paletteOne i b)|) (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _=> abs_nonneg _) (mem_univ i))
end sd

section beat
variable {Q : Picture G t} {U : Link G m→ℝ} {v : Breed t Bool}

def Bitter (l : ι → Stitch t) (F : Needle ι (Loc G 1) t) (v : Breed t Bool) (U : Link G m→ℝ) := liquid v U=∑ j,∑ i,pinRing (l i) (F j i) j m

lemma nectar {F : Needle ι (Loc G 1) t} {l : ι→Stitch t} (h : Dai F σ C) (hs : 0<σ) (he : Spool Q l F) (hx : DrinkIt Q U v) : Bitter l F v U := by
  apply relay_ext; intro p; let i := fun j=> (p j).2.2; let b := fun j=> (p j).2.1; let x := Prod.fst ∘ p
  rw [show (fun j => relay (p j).1 (p j).2)=glyph x i b from rfl, hx i b x]; unfold glyph collected
  let a (k : Fin (t+1)) := (b k,i k)
  simp_rw [_root_.sum_apply,pinRing_rec _ _ _ (h _ _) hs.le]; split
  next hz => rw [he _ _ _ (out_real x), mul_sum, Finset.sum_eq_single a]
             · simp [a,hz]
             · intro v hv hy; simp_rw [if_neg (show ¬ (v = (fun i' => (b i',i i')) ∧ ∑ j,x j=0) from fun hc => hy hc.1)]; simp
             simp
  next hz => simp [hz]
lemma nectar_run {T : Needle ι (Loc G 1) t} {l : ι→Stitch t} (g : Ratio c m) (h : Dai T (inch g.count*σ) C) (hv : Bitter l T v U) (p : Breed t (Site c)) (q : Breed t Momentum)
    (he : ∀ i,rolls (mon (p i)) (q i)) (hq : ∀ i,q i∈strip σ) (hs : 0<σ) (w : Breed t (Phase (Co g.count (Loc G 1)))) :
    liquid v U (fun i=> poured g (p i) (w i))= if ∑ i,p i=0 then (Fintype.card (Site c):ℂ)*tunnels l T q w else 0 := by
  have hz : 0 < inch g.count *σ := mul_pos (inch_pos _) hs
  unfold Bitter at hv; rw [hv,tunnels_green _ _ h hs hq]; simp_rw [_root_.sum_apply,flot_signal _ _ _ _ (h _ _) hz.le g he]; split <;> next hh=> simp [hh,mul_sum]
end beat
end YM.Stationary
end
