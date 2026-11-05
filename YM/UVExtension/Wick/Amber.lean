import YM.UVExtension.Wick.Sycamore

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} {z : Air f G} {Y : Config G c}

variable (R)
variable {ι : Type*} [Fintype ι] (W : ι → Juice G f)
-- Use branch logs: hol when beta near positive. weight non-analytic comparison reparameterized outside.
def amber (A : Stores S) := ((X.pens A).card* (Fintype.card G.ColorIndex:ℝ))/2

def warmth (u : ℝ) (z : ℂ) (A : Stores S) (m : ℝ) := Complex.exp ((z-(u:ℂ))*(m:ℂ)+ (amber X A:ℂ)*(Complex.log z-(Real.log u:ℂ))) -- note
lemma warmth_real {u v : ℝ} (_hu : 0 < u) (hv : 0<v) (A : Stores S) (m : ℝ) : warmth X u v A m=
    (Real.exp ((v-u)*m+amber X A*(Real.log v-Real.log u)):ℂ) := by unfold warmth; push_cast; rw [← Complex.ofReal_log hv.le]
lemma warmth_same {u v : ℝ} (z : ℂ) (A : Stores S) (m : ℝ) (hv:0<v) : warmth X u z A m=warmth X u v A m * warmth X v z A m:= by
  unfold warmth; rw [← Complex.exp_add, ← Complex.ofReal_log hv.le]; congr 1; ring
lemma warmth_size (z:ℂ) (A : Stores S) (m : ℝ) (h : 0<z.re) : ‖warmth X z.re z A m‖ = Real.exp (amber X A * Real.log (‖z‖/ z.re)) := by
  unfold warmth; have hp:0<‖z‖ := h.trans_le (Complex.re_le_norm z)
  simp [Complex.norm_exp, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.log_re,Real.log_div hp.ne' h.ne']
lemma warmth_diff {E:Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S': Set E} {f:E→ℂ} (hf:DifferentiableOn ℂ f S')
    (hp : ∀ x∈S',0<(f x).re) (v : ℝ) (A : Stores S) (m : ℝ) : DifferentiableOn ℂ (fun x=> warmth X v (f x) A m) S':=
    (((hf.sub_const _).mul_const _).add (((hf.clog (fun i hi => Or.inl (hp i hi))).sub_const _).const_mul _)).cexp
lemma trackV (A : Stores S) (hu : 0<u) (hv : 0<v) (h : LocalRatio Z) :
    (X.pens A).card * Real.log (measure_g Z v) = (X.pens A).card * Real.log (measure_g Z u) - amber X A*(Real.log v-Real.log u):= by
  have hh (t:ℝ) (ht:0<t): Real.log (measure_g Z t)= Real.log Z.scale+(Fintype.card G.ColorIndex:ℝ)*
      (Real.log (Real.sqrt (2*Real.pi))- Real.log t/2):= by
    unfold measure_g gStep; rw [Real.log_mul h.scale.ne' (by positivity),Real.log_pow,
      Real.log_mul (by positivity) (by positivity),Real.log_inv,Real.log_sqrt ht.le]; ring
  rw [hh v hv,hh u hu]; unfold amber; ring

def roots (u : Directions G f) (U : Config G f) (A : Stores S) := -(chalky X u U A+ crispy X A)
def barks (u : Directions G f) (A : Stores S) := -(X.quoteNear A u+ X.far_bills A)
variable {R}
lemma steer_plume (y : Directions G f) (U : Config G f) (A : Stores S) (hu:0<u) (hv:0<v) (h : LocalRatio Z) :
    plumeLog X a (flight R v) Z y U A=plumeLog X a (flight R u) Z y U A+(v-u)*roots X y U A+amber X A*(Real.log v-Real.log u):= by
  unfold plumeLog roots; dsimp only [flight]; rw [trackV X A hu hv h]; ring
lemma steam_root (y : Directions G f) (A : Stores S) (hu:0<u) (hv:0<v) (h : LocalRatio Z) :
    X.steamLog (flight R v) Z a A y=X.steamLog (flight R u) Z a A y+(v-u)*barks X y A+amber X A*(Real.log v-Real.log u):= by unfold steamLog barks; dsimp only [flight]; rw [trackV X A hu hv h]; ring
lemma plume_warm (y : Directions G f) (U : Config G f) (A : Stores S) (hu:0<u) (hv:0<v) (h : LocalRatio Z) (k : Finset ℕ) :
    (Polar.stock X a (flight R v) s Z y U k A:ℂ) = warmth X u v A (roots X y U A)*(Polar.stock X a (flight R u) s Z y U k A:ℂ) := by
  rw [warmth_real X hu hv]; rw [← Complex.ofReal_mul]; apply congr_arg Complex.ofReal; unfold Polar.stock; split; swap; · rw [mul_zero]
  next hZ =>
    dsimp only
    rw [steer_plume X y U A hu hv h]; rw [show Contract.order (flight R v) _ _ U=Contract.order (flight R u) _ _ U from (rfl : Contract.order (flight R v) k (vias S A (300*X.B)) U=Contract.order (flight R u) k _ U)] -- if LET
    rw [Real.exp_add,Real.exp_add,Real.exp_add]; ring
def rawP (R : Rep G f) (Ñ : ChartRatio G) (k : Finset ℕ) (s a : ℝ) (m : ℕ) (p : Stores S) (y : Directions G f) :=
    if Packets.connected S m X.B p then X.Pack R Ñ k s a p y else 0

lemma steam_warm (y : Directions G f) (A : Stores S) (hu:0<u) (hv:0<v) (h : LocalRatio Z) (k : Finset ℕ) (m:ℕ):
    (rawP X (flight R v) Z k s a m A y:ℂ) = warmth X u v A (barks X y A)*(rawP X (flight R u) Z k s a m A y:ℂ) := by
  rw [warmth_real X hu hv]; rw [← Complex.ofReal_mul]; apply congr_arg Complex.ofReal; unfold rawP Pack; split_ifs; swap; · rw [mul_zero]
  · unfold steam; dsimp only; rw [steam_root X y A hu hv h]; rw [show Contract.order (flight R v) _ _ _=Contract.order (flight R u) _ _ _ from (rfl : Contract.order (flight R v) k (vias S A (300*X.B)) _=Contract.order (flight R u) k _ (X.input y))]
    rw [Real.exp_add,Real.exp_add,Real.exp_add]; ring
  rw [mul_zero]

-- at height ONE. Equivalent expressions shifted to estimates at u via lemmas.
-- `y` for polar physical link exp coordinate, `U` includes actual held values.
def fireball (R : Rep G f) (Ñ : ChartRatio G) (s a : ℝ) (k : Finset ℕ) (m : ℕ) (W : ι → Juice G f)
    (β : ℂ) (V : ι → ℂ) (z : Air f G) : Head S → ℂ :=
    let y := X.μ+X.atmos z
    Sum.elim (fun t => warmth X 1 β t (barks X y t) * rawP X (flight R 1) Ñ k s a m t y) (Sum.elim
      (fun t => ∑ i, V i*(X.bag (chunk R (W i) 1) a y t:ℂ)) (Sum.elim
        (fun t => Complex.exp (logRay X R W a Ñ z β V t)-1)
        (fun t => (X.detect y s a R k t:ℂ))))

def amberP (R : Rep G f) (Ñ : ChartRatio G) (s a : ℝ) (k : Finset ℕ) (m : ℕ) (W : ι → Juice G f)
    (β : ℂ) (V : ι → ℂ) (z : Air f G) (y : Directions G f) (U : Config G f) : Head S → ℂ :=
    Sum.elim (fun t => if Packets.connected S m X.B t then warmth X 1 β t (roots X y U t) * (Polar.stock X a (flight R 1) s Ñ y U k t:ℂ) else 0) (Sum.elim
      (fun t => ∑ i, V i*(sheath X a (chunk R (W i) 1) y U t:ℂ)) (Sum.elim
        (fun t => Complex.exp (valRay X R W a Ñ y U z β V t)-1) (fun t=> (Polar.sprinkle X a R s y U k t:ℂ))))
variable (V : ι → ℝ) {y : Directions G f} {U : Config G f} {m : ℕ} {W' : Finset ℕ}

lemma original (h : LocalRatio Z) (hv : 0<v) (p : Head S) : fireball X R Z s a W' m W v (fun i=>(V i:ℂ)) z p=
    (X.vertex (chunk R (blend W V) v) Z s a W' m (scaled v z) p:ℂ):= by
  let R':= chunk R (blend W V) v; have hp:R'=chunk R (blend W V) v:=rfl
  let y:= X.μ+X.atmos z; have hh:X.liftA R'.beta (scaled v z)=y:= gust X z hv
  rcases p with p|p|p|p
  · change warmth _ _ _ _ _ * (rawP _ _ _ _ _ _ _ _ y:ℂ)= (rawP _ R' _ _ _ _ _ _ (X.liftA _ _):ℂ)
    rw [hh]; exact (steam_warm X (R:=R) y p zero_lt_one hv h W' m).symm
  · unfold fireball; unfold vertex; dsimp only [Sum.elim]; change _= (bag X R' a (X.liftA _ _) p:ℂ)
    rw [hh,hp,(real_k X W R y 1 V p v a 1).1]; push_cast; rfl
  · change Complex.exp _-_= (Coat.raiseAir X _ _ _ _ p:ℂ); unfold Coat.raiseAir
    rw [Complex.ofReal_sub,Complex.ofReal_exp, (real_rays X W R (a:=a) (Z:=Z) (z:=z) y 1 hv V p).1]; rfl
  unfold fireball; unfold vertex; dsimp only [Sum.elim]; change _= (X.detect (X.liftA R'.beta _) s a R' W' p:ℂ); rw [hh]; rfl
lemma originalP (h : LocalRatio Z) (hv : 0<v) (p : Head S) : amberP X R Z s a W' m W v (fun i=>(V i:ℂ)) z y U p=
    (Polar.ember X a (chunk R (blend W V) v) s Z y U (scaled v z) W' m p:ℂ) := by
  unfold amberP; unfold Polar.ember; rcases p with p|p|p|p; all_goals dsimp only [Sum.elim]
  · split_ifs; · exact (plume_warm X (R:=R) y U p zero_lt_one hv h W').symm
    simp
  · rw [(real_k X W R y U V p v a 1).2]; push_cast; rfl
  · rw [Complex.ofReal_sub,Complex.ofReal_exp, (real_rays X W R y U hv V p|>.2)]; rfl
  rfl
end YM.UVExtension.Wick
