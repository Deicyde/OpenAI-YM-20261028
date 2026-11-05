import YM.TraceExtension.Det.Hull
import YM.Next.STATIONARY.OneLoop.MomentumIntegral
set_option autoImplicit false
/-!
# SUITES. Use simple invariant IR regulator both bonds and sites; absolute
power count from uniform Fleets for any cell profile with established Jar.
-/
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience
open scoped BigOperators Topology ContDiff ComplexConjugate
variable {ι κ α : Type} [Fintype α] [DecidableEq α] {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n:ℕ}{σ τ A C D μ δ ε a r:ℝ}
def icing (α κ:Type)[Fintype α][DecidableEq α](μ:ℝ):Film κ α α:= Film.cardF (fun _ => ((μ^2:ℝ):ℂ) • 1)
lemma ice_w (X: Burst ι κ)(α: Type)[Fintype α][DecidableEq α] {T μ:ι→ℝ}(h:ColdR X T μ r): Week X T (μ^2) (fun i=> icing α κ (μ i)):=by
    let U:=Film.cardF (ι:=κ) (fun _=> (1:CompM α α))
    have ht:Week X T 1 (fun _=>U):=Week.holds (fun i=>(h.lower i).le) _
    have hp:=ht.airshift (M:=μ^2) (fun i=> ((μ i^2:ℝ):ℂ)) (fun i=>by rw[Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]; rfl)
    rw[mul_one] at hp; rw[show (fun i=> icing α κ (μ i))=(fun i=>U.weight (((μ i^2:ℝ)):ℂ)) from funext fun i=>by unfold icing U Film.cardF Film.weight; simp; rfl];exact hp
def alp (G:Gauge)(μ:ℝ)(T:KindF G):= (granary G T).plus (icing _ _ μ)
def quick (μ:ℝ)(G:Gauge)(T:KindF G): Award G := ((↑(1/2:ℝ)):ℂ) • (alp G μ T).figure - (cinder G μ).figure
lemma alp_m {T:KindF G}(h: Ticket T (fineFlare p M (m:=f))): Ticket (alp G μ T) (fun x=> Det.stock p M μ (input G f x)):=by
    have he : Jaunt (m:=f) (approached (μ^2 • (1:Matrix (Lines G f 1) (Lines G f 1) ℝ))) (fun _=> ((μ^2:ℝ):ℂ) • (1:CompM (Fslot G) (Fslot G))) 0:=by rw[prom_tone,prom_one'];exact Jaunt.smul Jaunt.noop _
    let F:= pelt_ticket (G:=G) (m:=f); exact (h.plus (F.pay F.rear)).plus (Ticket.current _ _ he)
lemma quick_receipt {T:KindF G}(h: Ticket T (fineFlare p M (m:=f))) (hp: 0<μ)(hm: (Det.stock p M μ (1:Config G f)).det ≠ 0): Awards (quick μ G T) (Det.marke p M μ ∘ input G f):= by
    let P := fun x => Det.stock p M μ (input G f x); let V := fun x => ammo μ (input G f x)
    have he : IsUnit (P 0).det := by unfold P; rw[input_zero];exact hm.isUnit
    have hy := ring_award (Equiv.refl _) (Equiv.refl _) (A:=P) (B:=V) (alp_m h) crumb he (fund_det (ammo_safe _ hp))
    rw[show Det.marke p M μ ∘ input G f=((1/2:ℝ) • (fun z=> Real.log (P z).det))- (fun z => Real.log (V z).det) from funext fun i=>by change Real.log (P i).det/2-_=1/2*Real.log (P i).det-Real.log (V i).det; ring];exact hy
variable {F:KindF G}{B:Bed}
lemma alp_w (hw: HouseWord G B p D ε σ C δ F) {k:Momentum}(hp: star k=k): Stable ((alp G μ F).tab k) ((min ε 1)*pebWeight k μ):=by
    let K:=min ε 1; have HK:0 < K:= lt_min hw.positive zero_lt_one; have hy: K ≤ 1:= min_le_right ..; have hh: K ≤ ε:= min_le_left ..
    refine stable_real fun x=>?_ ; change K * pebWeight k μ*slug x^2≤ (dotProduct (star x) (((granary G F).tab k+ ((μ^2:ℝ):ℂ) • (1: CompM (Fslot G) (Fslot G))) *ᵥ x)).re
    rw [barePost hw _ hp,Matrix.add_mulVec,Matrix.add_mulVec,dotProduct_add,dotProduct_add,Matrix.smul_mulVec,one_mulVec,dotProduct_smul,slug_self,smul_eq_mul]; simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,sub_zero]
    have H:= rug_test hw.metric hw.pos hw.lower hp x; let U := pageD G 0 k
    have hx : (dotProduct (star x) ((U*(pageD G 0 (-k))ᵀ) *ᵥ x)).re=slug (Uᴴ *ᵥ x)^2 := by
      rw [← Matrix.mulVec_mulVec,page_rear _ hp, ← show Uᴴᴴ= U from Matrix.conjTranspose_conjTranspose U,vested, conjTranspose_conjTranspose,slug_self]
      rfl
    rw [hx,mul_assoc,pebWeight, show (shadeK k^2+μ^2)*slug x^2 = slug (Uᴴ *ᵥ x)^2 + slug (pageD G 1 k *ᵥ x)^2 + μ^2*slug x^2 by rw[pure_grade hp G x, add_mul,mul_pow]]
    nlinarith only [H, hy,hh,sq_nonneg (slug (Uᴴ *ᵥ x)),sq_nonneg (slug (pageD G 1 k*ᵥ x)), mul_nonneg (sq_nonneg μ) (sq_nonneg (slug x))]
lemma alp_t {μ T:ι→ℝ}{X:Burst ι (Fslot G)}{p:ι→Clip}{B:ι→Bed}{σ ν:ι→ℝ}{F: ι→KindF G} (h:ColdR X T μ r)(he:0 < ε)(hp:∀ i, HouseWord G (B i) (p i) D ε (σ i) C (ν i) (F i)): Tall X (T^2) (fun i=> alp G (μ i) (F i)):= by
    have hK:=lt_min he zero_lt_one
    refine solidT (a:=min ε 1*(1/64)) (fun i=>(alp_w (μ:=μ i) (hp i) (axes_real _)).mono ?_) (by positivity) (fun i=> pow_pos (h.lower i) _)
    rw[mul_assoc];exact mul_le_mul_of_nonneg_left (cold_safe h i) hK.le
end YM.Trace.Loft
