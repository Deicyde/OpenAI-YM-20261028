import YM.EveryPhase.Cross
import YM.Euclid.Window

/-! # Bind to the normalized enclosing-shell rule. Use Euclidean time on this side. -/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase.Stress
open Function Set Filter MeasureTheory Metric Boundary Next.BOUNDARY Mink Complex Probe Table
open Work.C20 Next.BOUNDARY.Descent
open scoped Topology BigOperators LineDeriv
variable {n d : ℕ}

def first (j : Fin (n+1)) : Equiv.Perm (Fin (n+1)) where
  toFun := Fin.cons j j.succAbove
  invFun := hole j Fin.succ 0
  left_inv i := by refine Fin.cases ?_ ?_ i <;> simp
  right_inv i := by refine Fin.succAboveCases j ?_ ?_ i <;> simp

lemma first_coord (j : Fin (n+1)) : first j 0=j := rfl
lemma first_next (j : Fin (n+1)) (k : Fin n) : first j k.succ=j.succAbove k := by
  simp [first]
lemma hole_first {A : Type*} (j : Fin (n+1)) (v : Fin n → A) (a) : hole j v a ∘ first j=Fin.cons a v := by
  funext i; refine Fin.cases ?_ ?_ i <;> simp [first_coord,first_next]
lemma seat_first (j : Fin (n+1)) (x : Points n) (y : E4) : Points.rearrange (first j) (seat j x y)=Points.cons y x := by
  ext1 i; refine Fin.cases ?_ ?_ i <;> simp [first_coord,first_next, Points.cons]

def pureU (x : Points n) : Times n := fun i => (YM.time (x i) : ℂ)*I
def pureDock (x : Points n) : Dock n := ((Boundary.trace x,pureU x),0)
lemma pure_time {x : Points n} (hx : x∈ordered n) : pureU x ∈ strict n := by
  intro i j hj; simp [pureU]; exact hx hj
lemma pure_lay (x : Points n) : laid (Boundary.trace x) (pureU x)=wickSlice n x := by
  rw [wick_glow,laid]; congr 2
  all_goals (funext i; simp [pureU,readings])
lemma ink_hole {G : Gauge} {L : Register G} {S : Table L} (v : Fin n → S.Tag) (j : Fin (n+1)) (i : S.Tag) :
    Bid.ink (hole j v i)=hole j (Bid.ink v) (S.pin i.1 i.2) := by
  funext k; refine Fin.succAboveCases j ?_ ?_ k
  · unfold Bid.ink; rw [hole_self,hole_self]
  intro k; unfold Bid.ink; rw [hole_next,hole_next]
lemma sets_scene (x : Points n) (y : E4) (j : Fin (n+1)) :
    hole j (pureU x) ((YM.time y:ℂ)*I) = pureU (seat j x y) := by
  funext i; refine Fin.succAboveCases j ?_ ?_ i <;> simp [pureU]
lemma opens_scene (x : Points n) (y : E4) (j : Fin (n+1))
    (h : hole j (pureU x) ((YM.time y:ℂ)*I)∈strict (n+1)) : seat j x y ∈ ordered (n+1) := by
  rw [sets_scene] at h
  intro p q hp; simpa only [pureU,Complex.mul_I_im,ofReal_re,readings] using! h hp
lemma lodge_sets (j : Fin (n+1)) (x : Points n) (y : E4) :
    lodge j (Boundary.trace x) (pureU x) (spatial y) ((YM.time y:ℂ)*I) = wickSlice _ (seat j x y) := by
  rw [lodge,sets_scene]
  rw [show hole j (Boundary.trace x) (spatial y)= Boundary.trace (seat j x y) by
    funext i; refine Fin.succAboveCases j ?_ ?_ i <;> simp [Boundary.trace],pure_lay]
lemma ordered_conf {x : Points n} (h : x∈ordered n) : x∈conf n := place_same x ▸ clear (y:=readings x) h (Boundary.trace x)

-- relabel spectators to prepared shell, moving B to 0
-- leave stress first
def linger (v : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) where
  toFun := Fin.cons (α:=fun _ => Fin (n+1)) 0 (fun i => (v i).succ)
  invFun := Fin.cons (α:=fun _ => Fin (n+1)) 0 (fun i => (v.symm i).succ)
  left_inv i := by refine Fin.cases ?_ ?_ i <;> simp
  right_inv i := by refine Fin.cases ?_ ?_ i <;> simp

variable {G : Gauge} {L : Register G} {S U : Table L} {W : Surface S}
  {D : ∀ n, Blanket n} {Z : W.Aurora D} {P : DiffPlan S} {H : S.RealSpin} {F : Waves S}

-- define Euclidean densities, with B moved front. B given at weight d.

def ordering (S U : Table L) (v : Fin n → S.Tag) (x : Points (n+1)) (k : Fin (n+1)) (B : S.Tag)
    (a : S.Tag) (y : E4) := S.useAt U (Points.cons y (Points.rearrange (first k) x)) (Fin.cons a (Fin.cons B v))
lemma order_corr (U : Table L) (hU : U.Symmetric) (v : Fin n → S.Tag) (x : Points (n+1)) (k : Fin (n+1)) (B : S.Tag)
    (a : S.Tag) (y : E4) (j : Fin (n+2)) (hx : seat j x y∈conf (n+2)) :
    S.useAt U (seat j x y) (hole j (hole k v B) a)=ordering S U v x k B a y := by
  have hz := Points.rearrange_in (first j) hx; rw [seat_first] at hz
  rw [← S.class_perm U hU (first j) hx,seat_first,hole_first, ← S.class_perm U hU (linger (first k)) hz]
  unfold ordering; congr 1
  · ext1 i; refine Fin.cases ?_ ?_ i
    · simp [linger,Points.cons]
    intro l; simp [Points.cons,linger]
  funext i; refine Fin.cases ?_ ?_ i
  · simp [linger]
  intro l; simp [linger]; exact congr_fun (hole_first k v B) l

def curtain (U : Table L) (K : Killing) (T : S.Stress) (v : Fin n → S.Tag) (x : Points (n+1)) (k : Fin (n+1))
    (B : S.Tag) (a : Axis) (y : E4) := ∑ b : Axis, K.we b y * ordering S U v x k B ⟨4,T a b⟩ y

lemma waveT_pure (hU : U.Hierarchy) (hF : F.Region U) (hZ : Z.FullBody F) (K : Killing) (T : S.Stress) (v : Fin n → S.Tag)
    (x : Points (n+1)) (k : Fin (n+1)) (j : Fin (n+2)) (B : S.Tag) (a : Axis) (y : E4)
    (h : hole j (pureU x) ((YM.time y:ℂ)*I) ∈ strict (n+2)) :
    waveT Z K (Bid.ink (hole k v B)) T j a (Boundary.trace x) (pureU x) ((YM.time y:ℂ)*I) (spatial y)=
      curtain U K T v x k B a y := by
  unfold waveT tide; rw [lodge_sets]; unfold curtain
  apply Finset.sum_congr rfl; intro b _; rw [K.w_wick,seat_seat,
    show hole j (Bid.ink (hole k v B)) (S.pin 4 (T a b))=Bid.ink (hole j (hole k v B) ⟨4,T a b⟩) from
      (ink_hole (hole k v B) j ⟨4,T a b⟩).symm,emit_root hF hZ _ (opens_scene x y j h),
    order_corr U hU.laws.toSymmetric v _ _ _ _ _ _ (ordered_conf (opens_scene x y j h))]

lemma one_variable (v : Fin n → S.Tag) (q : Points (n+1)) (d : ℕ) (U : Table L) :
    ∃ A : S.Field d →ₗ[ℂ] ℂ, ∀ w, A w=S.useAt U q (Fin.cons ⟨d,w⟩ v) := by
  let r := fun i : Fin n => (⟨(v i).1,S.representative _ (v i).2⟩ : L.Token)
  refine ⟨(U.injectFront r q d).comp (S.representative d), ?_⟩
  intro w; rw [LinearMap.comp_apply,U.head_read]
  let t := Fin.cons (α:=fun _ => S.Tag) (⟨d,w⟩ : S.Tag) v
  have he : S.useAt U q t= U.read q (fun i => ⟨(t i).1,S.representative _ (t i).2⟩) := rfl
  rw [he]
  congr 1; funext i; refine Fin.cases ?_ ?_ i
  · rfl
  intro l; rw [Fin.cons_succ]; exact congr_arg (fun s : S.Tag => (⟨s.1,S.representative s.1 s.2⟩ : L.Token))
    (show t l.succ=v l from Fin.cons_succ ..).symm

lemma we_split (K : Killing) (x y : E4) (A Y : M4) (ha : K.V=A+Y) (hs : spaceLikeGen A) (ht : boostLike Y) (b) :
    K.we b y=K.we b x + (M4.move A (y-x) b : ℂ)+(-I)*(M4.move (Y*theta) (y-x) b:ℂ) := by
  have hw (p : E4) : K.we b p = zeta b*(K.translation b:ℂ)+(∑ i : Axis, Killing.tilted K.V b i * (p i:ℂ)) := by
    unfold Killing.we Killing.w
    rw [mul_add,Finset.mul_sum]; refine congr_arg (zeta b*(K.translation b:ℂ) + ·) ?_
    exact Finset.sum_congr rfl fun i _ => by unfold Killing.tilted; ring
  simp only [hw,ha,Killing.tilted_add,Killing.tilted_space hs,Killing.tilted_boost ht,
    M4.at_coord,PiLp.sub_apply,ofReal_sum,ofReal_mul,ofReal_sub,add_assoc,Finset.mul_sum]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  refine congr_arg (zeta b*(K.translation b:ℂ) + ·) ?_; exact Finset.sum_congr rfl fun i _ => by ring

-- tested Euclidean charge

def grounds (U : Table L) (K : Killing) (T : S.Stress) (v : Fin n → S.Tag) (x : Points (n+1)) (k : Fin (n+1)) (B : S.Tag)
    (χ : E4 → ℝ) (y : E4) := ∑ a : Axis, ((Analysis.D (basis a) χ y : ℝ) : ℂ)*curtain U K T v x k B a y

def taskE (U : Table L) (K : Killing) (R : S.Rotation) (P : DiffPlan S) (v : Fin n → S.Tag) (x : Points (n+1)) (k : Fin (n+1))
    (t : S.Tag) := S.useAt U x (hole k v ⟨t.1,rankAction R t.1 K.V t.2⟩)+∑ b : Axis,
      K.we b (x k) * S.useAt U x (hole k v ⟨t.1+1,P.deriv t.1 b t.2⟩)

lemma euclidean_shell (U : Table L) (K : Killing) (P : DiffPlan S) (T : S.Stress) (R : S.Rotation) (v : Fin n → S.Tag)
    (x : Points (n+1)) (hx : x∈conf (n+1)) (k : Fin (n+1)) (B : S.Tag) (hU : U.Hierarchy)
    (hh : StressLaws U T P.deriv R.lie) (χ : E4 → ℝ) (hχ : Window (Points.rearrange (first k) x) χ) :
    Integrable (grounds U K T v x k B χ) ∧ -(∫ y, grounds U K T v x k B χ y)=taskE U K R P v x k B := by
  obtain ⟨A,Y,ha,hA,hY⟩ := tangent_parts K.ok
  let c : Ortho.Skew := ⟨A,hA.1⟩
  let e : Ortho.Skew := ⟨Y*theta,off_skew hY⟩
  let f (a b : Axis) (w : E4→ℂ) (y : E4) := (((Analysis.D (basis a) χ y : ℝ) : ℂ) * w y)* ordering S U v x k B ⟨4,T a b⟩ y
  let X := Points.rearrange (first k) x
  have h0 : X 0=x k := by simp [X,first_coord]
  have hv := Points.rearrange_in (first k) hx
  have h a b w (hw : Continuous w) : Integrable (f a b w) := integrableShell hv hχ hU.smooth _ a w hw
  have hf a b : Integrable (f a b (K.we b)) := h a b _ (by unfold Killing.we Killing.w; fun_prop)
  have hm (y) : grounds U K T v x k B χ y=∑ a : Axis, ∑ b : Axis, f a b (K.we b) y := by
    simp only [grounds,curtain,f,mul_assoc, Finset.mul_sum]
  have ht a : Integrable (fun y => ∑ b : Axis, f a b (K.we b) y) := integrable_finsetSum _ fun b _ => hf a b
  constructor
  · change Integrable (fun y => grounds U K T v x k B χ y)
    simp_rw [hm]; exact integrable_finsetSum _ fun a _ => ht a
  let W (b : Axis) (r : Ortho.Skew) (y : E4) := (M4.move r.val (y-X 0) b:ℂ)
  have hw b r : Continuous (W b r) := by unfold W; apply continuous_ofReal.comp; simp_rw [M4.at_coord]; fun_prop
  have he (a b) : (∫ y, f a b (K.we b) y) = K.we b (x k)*(∫ y, f a b (fun _ => 1) y)+
      ((∫ y, f a b (W b c) y)+ (-I)*(∫ y, f a b (W b e) y)) := by
    rw [show f a b (K.we b)=fun y => K.we b (x k)*f a b (fun _ => 1) y+(f a b (W b c) y+ (-I)*f a b (W b e) y) by
      funext y; dsimp only [f,W,c,e]; rw [h0,we_split K _ _ _ _ ha hA hY]; ring]
    have ht : Integrable (fun y => f a b (W b c) y+ (-I)*f a b (W b e) y) :=
      (h a b _ (hw b c)).add ((h a b _ (hw b e)).const_mul _)
    rw [integral_add ((h a b (fun _ => 1) continuous_const).const_mul (K.we b (x k))) ht,
      integral_add (h a b _ (hw b c)) ((h a b _ (hw b e)).const_mul (-I)),integral_const_mul,integral_const_mul]
  let D₁ (b : Axis) := shellGrad U T χ b X v B.2
  let D₂ (b : Ortho.Skew) := shellSpin U T χ b X v B.2
  have he₁ b : (∑ a : Axis, ∫ y, f a b (fun _ => 1) y)= - D₁ b := by
    simp [D₁,shellGrad, ordering,X,f]
  have he₂ r : (∑ a : Axis, ∑ b : Axis, ∫ y, f a b (W b r) y)= -D₂ r := by
    simp [D₂,shellSpin, W,X,f,ordering]
  have hr : rankAction R B.1 K.V B.2 = R.lie B.1 c B.2 + (-I) • R.lie B.1 e B.2 := by
    rw [ha,map_add,rank_space R _ hA, rank_boost R _ hY]; rfl
  have hq t : S.useAt U x (hole k v t)= S.useAt U X (Fin.cons t v) := by
    rw [← S.class_perm U hU.laws.toSymmetric (first k) hx,hole_first]
  have hD (b : Axis) : D₁ b = S.useAt U x (hole k v ⟨B.1+1,P.deriv _ b B.2⟩) := (hh.translation hv v hχ b B.1 B.2).trans (hq _).symm
  have hH : D₂ c+(-I)*D₂ e=S.useAt U x (hole k v ⟨B.1,rankAction R B.1 K.V B.2⟩) := by
    have hz b : D₂ b=S.useAt U X (Fin.cons ⟨B.1,R.lie B.1 b B.2⟩ v) := hh.rotation hv v hχ b B.1 B.2
    obtain ⟨M,hM⟩ := one_variable v X B.1 U
    rw [hz,hz,hq,hr]; simp_rw [← hM]; simp
  unfold taskE; simp_rw [hm]
  rw [← hH,integral_finsetSum _ (fun a _ => ht a)]
  simp_rw [integral_finsetSum _ (fun b _ => hf _ b),he,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f:=fun a b => K.we b (x k)*(∫ y, f a b (fun _ => 1) y)),he₂]
  simp_rw [← Finset.mul_sum]; rw [he₂]; simp_rw [he₁,hD]; simp; ring
end YM.EveryPhase.Stress
