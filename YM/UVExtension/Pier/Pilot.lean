import YM.UVExtension.Rafter.Flight
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Sails
import YM.Extra.SOURCE_HISTORIES.Dressing
/-! # Normalized E/K insertion functional, fixed in-place recipe

Sup rather than high jets. Even in scratch bounds use this at the VERY addresses
of the calibrated density (labels and tests included). A multipoint insertion
is going to travel as a **single** detached/disconnected mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Pier
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet Extra.Histories MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}
variable (B: BudgetPoint) (w: Wing)
local notation "C"=> Config G n
variable (n G)
-- common addresses via receipt (HasSlots)
def land (w:Wing) : Support n:= match w with
 | .logKey i => ((drawer G n).reg i).support
 | .gasKey i => (Ovens.Pipes.addr (folio G n) B i).support
def blot (w:Wing)(U:Config G n):Prop:= match w with
 | .logKey _ => Healthy B.threshold (land G n B w) U
 | .gasKey i => (Ovens.Pipes.addr (folio G n) B i).eligible B.threshold U
variable {G n}
variable {Q : Rep G n}
local notation "X"=> land G n B w
variable {B}
lemma whereAt (hq:Q.p=B)(h:HasSlots Q.p Q.activities): w.support Q= land G n B w:=by cases w<;> simp only [Wing.support,h.reg,h.forced,hq] <;> rfl
lemma sortBit (hq:Q.p=B)(h:HasSlots Q.p Q.activities)(U:Config G n): w.qualifies Q U ↔ blot G n B w U:=by cases w <;> simp only [Wing.qualifies,h.reg,h.forced,hq] <;> rfl
variable (B)
def Quiet (G:Gauge)(n: Side)(B: BudgetPoint) (w:Wing) := ∀ R:Rep G n,R.p=B → HasSlots R.p R.activities→ w.blank R
lemma letter (x:Support n)(hx:(0:Site n)∈x): Quiet G n B (.logKey (Blush.found 0 x hx)):=fun _ _ h=>h.regular _
lemma gas (i:ℕ): Quiet G n B (.gasKey i):=fun _ _ _=>trivial
variable {B} in
lemma stamp (x:Support n)(hx:(0:Site n)∈x)(hQ:Q.p=B)(hp:HasSlots Q.p Q.activities): land G n B (.logKey (Blush.found 0 x hx))=x:=by rw [← whereAt _ hQ hp,Wing.support,Blush.latch Q 0 x hx hp]
structure Held (B:BudgetPoint)(w:Wing)(f:Config G n→ℂ) : Prop where
   read : UsesFinal B.threshold (land G n B w) f
   scope U:f U ≠ 0 → blot G n B w U
   here : f ≠ 0→ (0:Site n)∈ land G n B w
   mesh : Measurable f
   symm : GaugeInvariant f
   paid : ∃ u:ℝ,∀ U, ‖f U‖ ≤ u

open BoundedContinuousFunction
def PoleC (B:BudgetPoint)(w:Wing) : Submodule ℂ (Config G n→ ℂ) where
   carrier:={x| Held B w x}
   zero_mem':= ⟨fun _ _ _ _=>rfl,fun _ h=>(h rfl).elim,fun h=>(h rfl).elim,measurable_const, fun _ _=>rfl,⟨0,by simp⟩⟩
   add_mem':=fun {x y hx hy}=>by
     have he : Held B w x:= hx; have h: Held B w y:=hy; obtain ⟨v,hv⟩:=he.paid; obtain ⟨u,hu⟩:=h.paid
     refine ⟨fun i j e E=> congr_arg₂ (·+·) (he.read i j e E) (h.read i j e E),?_,?_,he.mesh.add h.mesh,fun t U=> congr_arg₂ (·+·) (he.symm t U) (h.symm t U),v+u,fun U=> (norm_add_le ..).trans (add_le_add (hv U) (hu U))⟩
     · intro U hP; by_cases hQ: x U=0; · exact h.scope U (fun hE=>hP (by rw [Pi.add_apply,hQ,hE,add_zero]))
       exact he.scope U hQ
     intro hP; by_cases hQ:x=0; · exact h.here (fun hv=>hP (by rw [hQ,hv,add_zero]))
     exact he.here hQ
   smul_mem':=fun t x hx=>by
     have h:Held B w x:=hx; obtain ⟨v,hv⟩:= h.paid
     refine ⟨fun i j e E=>congr_arg (t • ·) (h.read i j e E),fun U he=>h.scope U (fun h=>he (by rw [Pi.smul_apply,h,smul_zero])),fun H=> h.here (fun h=> H (by rw [h,smul_zero])),h.mesh.const_smul _,fun a U=>congr_arg (t • ·) (h.symm a U),‖t‖*v,fun U=>?_⟩
     simp only [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (hv U) (norm_nonneg _)
variable (x:PoleC (G:=G) (n:=n) B w) (hq:Quiet G n B w)
lemma held : Held B w x.val:=x.property

def grow : PoleC (G:=G) (n:=n) B w→ₗ[ℂ] (Lab G n →ᵇ ℂ) where
    toFun:=fun x=> ofNormedAddCommGroupDiscrete (fun i=>x.val i.tag) (held _ _ x|>.paid.choose) (fun i=> (held _ _ x|>.paid.choose_spec i.tag))
    map_add' _ _:=DFunLike.ext _ _ fun _=>rfl
    map_smul' _ _:= DFunLike.ext _ _ fun _=>rfl
abbrev Pin:=twig (grow (G:=G) (n:=n) B w)
lemma charged {t:ℝ}: ‖Pin B w x‖ ≤ t ↔ ∀ U, ‖x.val U‖ ≤ t := by
   constructor; · exact fun h i=> ((grow B w x).norm_coe_le_norm ⟨i⟩).trans h
   intro h; exact (BoundedContinuousFunction.norm_le ((norm_nonneg _).trans (h 1))).2 (fun (i:Lab G n)=> show ‖grow B w x i‖≤_ from h i.tag)
variable (N : ℂ→L[ℝ] ℝ) (hN:∀ u, ‖N u‖ ≤ ‖u‖) (Q : Rep G n)(hQ:Q.p=B)(hp:HasSlots Q.p Q.activities)
def moor : Leaf Q where
   turn := w
   ingredient := N ∘ x.val
   scopedR:=by rw [whereAt _ hQ hp,hQ]; exact fun U V e E=>congr_arg N ((held _ _ x).read U V e E)
   grant:=fun U hv=> (sortBit w hQ hp U).2 ((held _ _ x).scope U (fun h=>hv (by change N _ = 0;rw [h,map_zero])))
   blank:=hq Q hQ hp
   weight:= ‖Pin B w x‖
   earn:=fun U=> (hN (x.val U)).trans ((charged B w x).mp le_rfl U)
   glows:=fun t U=>congr_arg N ((held _ _ x).symm t U)
   borel:= N.continuous.measurable.comp (held _ _ x).mesh
-- direct insertion density & exact value at a REAL Leaf. No fake receipt.
def port (Q : Rep G n)(w:Wing)(U:Config G n): ℂ:= match w with
 | .logKey _ => (Q.eval U:ℂ)
 | .gasKey i=> (Real.exp (Q.exponent U):ℂ) * dressed Q i U
lemma lit (M:Leaf Q) (U:Config G n): port Q M.turn U*(M.ingredient U:ℂ)=(M.cicada U:ℂ):=by
   cases h:M.turn with
   | logKey i=> rw [Blush.cliff Q i U M h]; exact (Complex.ofReal_mul ..).symm
   | gasKey i=> rw [Blush.fords Q i U M h]; unfold fare port; ring
-- no installations in assembly need quota for unanchored ports if file is zero
variable {σ v a r b:ℝ}
lemma pricing (h:Q.Lawful σ v a r b):∃ u:ℝ,∀ w U, ‖port Q w U‖ ≤ u:=by
   obtain ⟨s,hs⟩:= (Q.envelope h).cost; obtain ⟨t,ht⟩:= ((Q.exponentEnv h).exp).cost; obtain ⟨c,-,-,hv⟩:= dressed_budget h
   refine ⟨max s (t*c),fun w U=>?_⟩; cases w with
   | logKey i=> exact ((Complex.norm_real _).trans_le (hs U)).trans (le_max_left ..)
   | gasKey i=> unfold port; rw [norm_mul]; exact (mul_le_mul ((Complex.norm_real _).trans_le (ht U)) (hv i U) (norm_nonneg _) ((norm_nonneg _).trans (ht U))).trans (le_max_right ..)
lemma portEnv (h:Q.Lawful σ v a r b): Envelope (port Q w):=by
   obtain ⟨u,hu⟩:=pricing Q h; refine ⟨?_,u,hu w⟩; cases w with
   | logKey _=> exact Complex.continuous_ofReal.measurable.comp (Q.envelope h).meas
   | gasKey i=> exact (Complex.continuous_ofReal.measurable.comp (Q.exponentEnv h|>.exp.meas)).mul (dressed_meas h i)

def total (Q:Rep G n)(f:Config G n→ℂ):= (((∫ U,Q.eval U ∂prior G n):ℂ))⁻¹ * ∫ U,f U ∂prior G n
def hit (Q:Rep G n)(w:Wing)(f:Config G n→ℂ):= total Q (port Q w*f)
lemma payable (h:Q.Lawful σ v a r b) : Integrable (port Q w*x.val) (prior G n):= by
    have ht : Envelope x.val:= ⟨(held _ _ x).mesh,(held _ _ x).paid⟩
    exact ((portEnv w Q h).mulC ht).integrableC _

def tariff (h:Q.Lawful σ v a r b): PoleC (G:=G) (n:=n) B w→ₗ[ℂ] ℂ where
   toFun := fun x=>hit Q w x.val
   map_add' x y:=by change hit Q w (x.val+y.val)=_; unfold hit total; rw [mul_add]; simp only [Pi.add_apply]; rw [integral_add (payable B w x Q h) (payable B w y Q h),mul_add] -- elaboration
   map_smul' t x:=by change hit Q w (t • x.val)=_; unfold hit total; simp_rw [Pi.mul_apply,Pi.smul_apply,smul_eq_mul, mul_left_comm _ t, integral_const_mul]; exact mul_left_comm ..
end YM.UVExtension.Pier
