import YM.RG08.Fete.Repertoire
import YM.RG08.Trill.Cues
/-!
# Fk actual stencil charts on finite local addresses
Embedded with centered units. Spot boolean, no duplication. Builds stencil & prices separate.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Fete
open Function Finset Jetty Lattice Isles Forms Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Lagoon  Trill Exterior RG Precision -- namespaces maybeYurt
open scoped Classical ContDiff Topology BigOperators ENNReal Matrix.Norms.Frobenius ComplexConjugate
variable {G:Gauge}{d n p l e D:ℕ}{σ B:ℝ}
local notation "E"=>Ed G Cover
local notation "Y"=>Snap G d
variable {S:Finset Cover}

abbrev Matin (G:Gauge)(S:Finset Cover):= Spot S × G.ColorIndex
/-- label injection -/
def window (i:Matin G S):E:=((Place.first i.1).val,Exterior.coord (Place.beam i.1),i.2)
-- needed later aspect masks
lemma windows:Function.Injective (window (G:=G) (S:=S)):=by
 rintro ⟨⟨⟨⟨x,hx⟩,a⟩,hA⟩,i⟩ ⟨⟨⟨⟨y,hy⟩,b⟩,hB⟩,j⟩ H
 change (x,(Exterior.coord a,i))=(y,(Exterior.coord b,j)) at H
 simp only [Prod.mk.injEq] at H
 have ht:a=b:=by have := congrArg Quarry.back H.2.1;simpa using this
 cases H.1;subst b;cases H.2.2;rfl

def punch (G:Gauge)(S:Finset Cover): Cellar (Matin G S)→L[ℝ] Dev S G:=LinearMap.toContinuousLinearMap {
 toFun f s:=heavy G (fun i=>f (s,i))
 map_add':=by intros;rfl
 map_smul':=by intros;rfl}
/-- Snap to the same chart, actual log germ -/
def flume (z:Y):Cellar (Matin G S):=fun i=>hi i.2 (localLane z i.1)
lemma flume_smooth :ContDiffAt ℝ ω (@flume G d S) 0:=contDiffAt_pi.mpr fun i=>(hi i.2).contDiff.contDiffAt.comp (f:=fun z=>localLane (S:=S) z i.1) 0 (lane_smooth (G:=G) (d:=d) _ _)
lemma flume0:(@flume G d S) 0=0:=by unfold flume;rw [local_zero];funext x; rw [Pi.zero_apply,map_zero];rfl
lemma flume_full (z:Y): punch G S (flume z)=localLane z:=rfl
 set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
lemma flume_tint (i:Matin G S)(z:Y): Tensor.diagonal (Tensor.coeff flume n (0:Y)) z i = pluck n z (window i):=by
 let L:Cellar (Matin G S) →L[ℝ] ℝ:= ContinuousLinearMap.proj i
 have he : Pace (chord (window i) (d:=d)):=lane_smooth ..
 have ht : L ∘ (@flume G d S)=hi i.2 ∘ chord (window i):=by funext x; change _=hi i.2 (lane _ (Quarry.back (Exterior.coord (Place.beam i.1))) x);rw [Quarry.back_axis];rfl
 have h:=congrArg (fun f:Y→ℝ=>iteratedFDeriv ℝ n f 0) ht
 rw [L.iteratedFDeriv_comp_left flume_smooth (i:=n) (mod_cast le_top),(hi i.2).iteratedFDeriv_comp_left he (i:=n) (mod_cast le_top)] at h
 change (n.factorial:ℝ)⁻¹ * L (iteratedFDeriv ℝ n flume 0 (fun _=>z))=hi i.2 ((n.factorial:ℝ)⁻¹ • _); rw [show L (iteratedFDeriv ℝ n flume 0 (fun _=>z))=hi i.2 (iteratedFDeriv ℝ n (chord (window i)) 0 (fun _=>z)) from DFunLike.congr_fun h (fun _=>z),_root_.map_smul];rfl

variable {X:Labels.Frame G d}
/-- real normalized cylinder at local gauge chart. exact component via Sound.real. -/
def astro (T:SectionData X)(a:X.Index): Still (Matin G T.stencil):= fun x=> (Place.column T a (punch G T.stencil x)).re
 set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
lemma lamp (T:SectionData X)(a:X.Index): Pace (astro T a):=by
 let L:=punch G T.stencil
 change ContDiffAt ℝ ω (Complex.reCLM ∘ Place.column T a ∘ L) 0
 exact ((Complex.reCLM.contDiff.comp (Place.column_smooth T a)).comp L.contDiff).contDiffAt
lemma silence (T:SectionData X)(a:X.Index)(h:Bid.pop T)(n:ℕ)(hn:n<(X.grades a).2):Tensor.coeff (astro T a) n 0=0:=by
 let L:=punch G T.stencil
 change Tensor.coeff (Complex.reCLM ∘ Place.column T a ∘ L) n 0=0
 unfold Tensor.coeff
 rw [Complex.reCLM.iteratedFDeriv_comp_left (((Place.column_smooth T a).comp L.contDiff).contDiffAt) (show (n:WithTop ℕ∞)≤ω from le_top), Next.Foundations.jets_linear L ((Place.column_smooth T a).contDiffAt.of_le (mod_cast le_top)),Place.radials_vanish T h a n hn]
 ext;change (n.factorial:ℝ)⁻¹ • Complex.reCLM 0=(0:ℝ);simp
lemma astro_live (H:Hol G)(T:SectionData X)(h:T.Sound H)(a:X.Index)(x:Cellar (Matin G T.stencil)): (astro T a x:ℂ)=Place.column T a (punch G T.stencil x):=by
 let R:=column T a (punch G T.stencil x)
 have he:=h.ordinary_real (Place.copy X a) (pore (punch G T.stencil x))
 rw [show star (Place.copy X a)=Place.copy X a from ?_] at he;swap
 · funext i;by_cases ht:i=a; subst i; simp [Place.copy];simp [Place.copy, ht]
 have ht:=congrArg Complex.im (show R=star R from he); rw [Complex.star_def,Complex.conj_im] at ht
 change (↑R.re:ℂ)=R;apply Complex.ext;simp;simp;linarith

-- Chart Taylor ordered display on Cellar I generic.
section
variable {I:Type} [Fintype I]
def ton (f:Still I)(n:ℕ):Flake n I:=fun i=>Tensor.coeff f n 0 (Camera.billet ∘ i)
-- cast: Flake is real.
lemma ton_sym (f:Still I)(h:Pace f)(n:ℕ):Forms.Sym (ton f n):=fun i=>funext (fun j=> Tensor.coeff_symm (h.of_le (show (n:WithTop ℕ∞)≤ω from le_top)) (Camera.billet ∘ j) i)
lemma ton_comp (f:Still I)(v:Fin n→Cellar I) : Tensor.coeff f n 0 v=∑ i:Tape n I,ton f n i*(∏ j,v j (i j)):=by
 let M:=Tensor.coeff f n 0
 have ht: M v=M (fun j=>∑ i:I,v j i • Camera.billet i):=by
    apply congrArg M;funext j k; simp [Camera.billet,Finset.sum_apply,Pi.single_apply,mul_ite,smul_eq_mul]
 change M v=_;rw [ht,M.map_sum (fun i j=>v i j • Camera.billet j)];apply sum_congr rfl;intro i _;rw [M.map_smul_univ,mul_comm];rfl
lemma ton_parley (f:Still I)(h:Pace f)(n:ℕ): parley (ton f n)=Camera.print n f:=by
 apply MvPolynomial.funext;intro v;rw [parley_street,← Camera.flute,Camera.glimpses h n,← ton_comp f (fun (_:Fin n)=>v)];rfl -- def
end
end YM.RG08.Fete
