import YM.RG05Readout.Test.Common
import YM.RG05Readout.Address.Reprice
import YM.MergeProof.North.Amber
import YM.MergeProof.Cashew
import YM.Trace.Physicalv2.GermGraph
/-!
# Snapshot ports

Values, presented exponential and forced partners including old inventory on
this vacuum. Not treating equality of values as equality of these reps.
Finite-dimensional colors for the test polynomials and finite superpositions
of Tail atoms metrized at fixed order. Reclosure clients using this port must
actually emit such presentations / certify their referenced costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G: Gauge}{n:Side}{d e k:ℕ} {F:Labels.Frame G d} (P:Coefficient F n)(o:Site n)(B:SectionData F)(R:RG.Rep G n)

abbrev Goods (G:Gauge)(n:Side):=Config G n → ℂ
abbrev Three (G:Gauge)(n:Side):= Goods G n × Goods G n × (ℕ→Goods G n)
abbrev Tape (G:Gauge)(n:Side):= Body→ₗ[ℂ]Three G n
def invoice : Three G n := (P.density o B R,P.exponentialEntry o B R,P.forced)
lemma invoice_stretch (z:ℂ) : invoice (stretch z P) o B R=z • invoice P o B R:=by
    let Q:= stretch z P
    have hs: Q.exponentialEntry o B R=z • P.exponentialEntry o B R:=by
       funext U
       have ht i: Q.maskedTerm R i U=z * P.maskedTerm R i U:=masked_scale ..
       change part B o R U (z • P.x)+ (∑' j, Q.maskedTerm R j U)=z * (part B o R U P.x+∑' j, P.maskedTerm R j U)
       rw [map_smul]; simp_rw [ht,tsum_mul_left,mul_add, smul_eq_mul]
    exact Prod.ext (funext (stretch_density B R o z P)) (Prod.ext hs rfl)
lemma invoice_add (Q:Coefficient F n){σ C Λ δ w a b c:ℝ}(hr:R.Lawful σ C Λ δ w) (hP:P.remBound o R c a) (hQ: Q.remBound o R c b):
    invoice (beside P Q) o B R=invoice P o B R+invoice Q o B R:= Prod.ext (plus hr hP hQ B) (Prod.ext (duo_exp B hP hQ) (sideK ..))
lemma invoice_zero (B:SectionData F) (o:Site n) : invoice (Extra.Histories.primary o 0) o B R=0:=by
    let P:Coefficient F n:=Extra.Histories.primary o 0
    apply Prod.ext (funext fun U=> by change P.density o B R U=0; rw [primary_density,map_zero,mul_zero]); refine Prod.ext ?_ rfl
    funext U; have ht i:P.maskedTerm R i U=0:= congr_fun (map_zero (maskLinear _ _)) _
    change part B o R U 0+ (∑' i,P.maskedTerm R i U)=0;rw [map_zero];simp_rw [ht,tsum_zero,add_zero]
structure Useful (x:Three G n):Prop where
    normK : Dominated x.2.2
    read : Accent.coin R x.2.1 x.2.2=x.1
    integr : Integrable x.1 (prior G _)

lemma Useful.invoice {σ C Λ δ w a c:ℝ} {H:Hol G}(hr:R.Lawful σ C Λ δ w) (hp:P.remBound o R c a)(hP:P.Format o H R): Useful R (Address.invoice P o B R):=by
   refine ⟨rem_dominated hp,Accent.coin_primary R _ _ _,?_⟩; have hs:=Coefficient.envelope B hr hp hP; obtain ⟨b,hb⟩:=hs.cost
   exact Integrable.of_bound hs.meas.aestronglyMeasurable b (.of_forall hb)
lemma Useful.zero : Useful R 0:= ⟨Float.pawn0,funext (fun U=> by change Accent.coin R 0 0 U=0; rw [Float.coin₀]; simp), integrable_zero ..⟩
lemma Useful.smul (x:Three G n) (a:ℂ)(hp:Useful R x):Useful R (a • x):=by
   obtain ⟨h1,h2,h3⟩:=hp; refine ⟨?_ ,by change Accent.coin _ _ _=a • x.1; rw [show (a • x).snd.1=a • x.snd.1 from rfl, show (a • x).snd.2=a • x.snd.2 from rfl, coin_mul,h2], h3.smul a⟩
   obtain ⟨b,hb,hv⟩:=h1
   exact ⟨_,hb.mul_left ‖a‖,fun i u=> by change ‖a • (x.snd.2 i u)‖ ≤ _; rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hv i u) (norm_nonneg _)⟩
lemma Useful.join {σ C Λ δ w:ℝ} {x y:Three G n} (hr:R.Lawful σ C Λ δ w) (h:Useful R x)(H:Useful R y): Useful R (x+y):= ⟨Float.combn h.normK H.normK,(Float.coin_plus R _ _ h.normK H.normK hr.labels.boundK).trans (congr_arg₂ (·+·) h.read H.read),h.integr.add H.integr⟩
lemma Useful.family {ι:Type*} {σ C Λ δ w:ℝ} (hr:R.Lawful σ C Λ δ w)(s:Finset ι)(v:ι→Three G n) : (∀ i, Useful R (v i)) → Useful R (∑ i∈s,v i):=by
    intro h; classical induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact Useful.zero R
    | @insert i s hi ih => rw [Finset.sum_insert hi]; exact Useful.join R hr (h i) ih

-- linearized valuation tape of one atom
def glyph (f:PulseC)(x:Three G n): Tape G n where
   toFun φ:= f φ • x
   map_add' φ ψ:=by rw [map_add,add_smul]
   map_smul' b φ:=by rw [map_smul, smul_assoc]; rfl
@[simp]
lemma glyph_apply (f:PulseC)(x:Three G n)(φ:Body):glyph f x φ=f φ • x:=rfl
@[simp]
lemma glyph_zero (f:PulseC) : glyph f (0:Three G n)=0:=by ext1; simp
lemma glyph_plus (f:PulseC)(x y:Three G n):glyph f (x+y)=glyph f x+glyph f y:=by ext1; simp [smul_add]
lemma glyph_stretch (f:PulseC)(x:Three G n)(a:ℂ): glyph f (a • x)=a • glyph f x:=by ext1; simp [smul_comm _ a]
open Address -- maybe linter
open YM.MergeProof
variable {k t : ℕ} (S:Family G)
abbrev kept {d:ℕ}(i:Letter d):ℕ:= d-depth i
abbrev Palette (S:Family G) (d:ℕ):= (i:Letter d)→ S.label (kept i)
abbrev LevelStencil (C:Family G) (i:Letter d):= Coefficient (C.labels.level (kept i)) n

-- finite families. analytic input for reclosure would have to count also these absolute weight budgets.
inductive Necklace (T:Labels.Frame G 0)(Z:SectionData T)(H:Hol G)(R:Rep G n)(o:Site n) (κ:ℝ)(s:ℕ) : Tape G n → ℝ → Prop where
   | empty : Necklace T Z H R o κ s 0 0
   | chain {V:Tape G n}{r v t:ℝ}(f:PulseC)(hf: Native.Tail s f)(h:Native.Priced s f v) (u:Coefficient T n)(hu:u.Format o H R)(he:u.remBound o R κ r)(ht:Necklace T Z H R o κ s V t): Necklace T Z H R o κ s (glyph f (invoice u o Z R)+V) (v*(T.coeffSize u.x+r)+t)

local notation "S₀"=> S.localSection
local notation "Fᵢ"=> S.labels.level
set_option quotPrecheck false
abbrev lows (C:Family G)(n:Side)(d:ℕ):=(i:Letter d)→ Coefficient (C.labels.level (kept i)) n
def together (C:Family G) (R:Rep G n)(o:Site n)(d:ℕ)(P:lows C n d):Tape G n:= ∑ i: Letter d, glyph (readJ i 0) (invoice (P i) o (C.localSection (kept i)) R)

-- adopt pin's Germ.projection including winding for now. all alternative representations must use it to invoke these estimates.
open Trace.Physical
inductive Printed (C:Family G)(d:ℕ)(R:Rep G n) (o:Site n) (κ:ℝ)(V:Tape G n)(x y:Palette C d)(g:ℝ):Prop where
  | bind (P:lows C n d)(F:Tape G n) {v:Letter d→ℝ} {t:ℝ} (H: Necklace (C.labels.level 0) (C.localSection 0) C.params R o κ d F t) (placed:∀ i, (P i).Format o C.params R) (priced:∀ i,(P i).remBound o R κ (v i)) (actual:together C R o d P+F=V) (label : x=fun i=>(P i).x) (jet : y=fun i=> Trace.Physical.Germ.projection (C.labels.level (kept i)) C.params R.p.threshold o (P i)) (cost:(∑ i,v i)+t ≤ g)

end YM.RG05Readout.Address
