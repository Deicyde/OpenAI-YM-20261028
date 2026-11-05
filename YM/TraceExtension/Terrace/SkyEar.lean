import YM.TraceExtension.Terrace.Traveller
import YM.TraceExtension.Terrace.Lease
import YM.TraceExtension.Terrace.Ears
import YM.Next.UV_STRESS.Gate
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Finset Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis StressFlux Next.UVStress
open Further.PhysicalPeriodLimitF933 Next.Rank.Spindle Cells PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Next.Rank.Station
open UVNext.FreeStress (camera)
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
def nearPoint (x:ℝ):Cover:= fun i=> if i=0 then ⌈x⌉ else 1
lemma clearNear {x t:ℝ}(hx:0<x)(ht:0<t): Extraction.tag t (![nearPoint x,0]: Fin 2→ Cover)∈generic 2:=by
    intro a u v h
    have hp:0<Int.ceil x:=Int.ceil_pos.mpr hx
    have he:(nearPoint x a:ℝ) ≠ 0:=by unfold nearPoint;split <;> positivity
    fin_cases u <;> fin_cases v <;> simp_all [Extraction.tag]
lemma nearing {b:ℕ→ℝ}(ht:Tendsto b atTop atTop) (h:∀ i,0<b i): Tendsto (fun i=> Extraction.tag (b i)⁻¹ (![nearPoint (b i),0]:Fin 2→ Cover)) atTop (𝓝 (camera 0)):=by
    let M:=fun i=> Extraction.tag (b i)⁻¹ (![nearPoint (b i),0]:Fin 2→ Cover)
    let q:=camera 0; have hx:= tendsto_inv_atTop_zero.comp ht
    have he:Tendsto (fun i=> (b i)⁻¹*(Int.ceil (b i):ℝ)) atTop (𝓝 1):=by
       refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds (x:=(1:ℝ))) (show Tendsto (fun i=>1+(b i)⁻¹) atTop (𝓝 1) from by simpa using! hx.const_add 1) ?_ ?_
       · intro i; rw [← inv_mul_cancel₀ (h i|>.ne')]; exact mul_le_mul_of_nonneg_left (Int.le_ceil _) (inv_pos.mpr (h i)).le
       intro i; apply (mul_le_mul_of_nonneg_left (Int.ceil_lt_add_one _|>.le) (inv_pos.mpr (h i)).le).trans; rw[mul_add,inv_mul_cancel₀ (h i|>.ne'),mul_one]
    have hp (u:Fin 2) (i:Axis): Tendsto (fun j=> M j u i) atTop (𝓝 (q u i)):=by
       fin_cases u
       · change Tendsto (fun j=>(b j)⁻¹*(nearPoint (b j) i:ℝ)) _ (𝓝 (basis 0 i))
         by_cases hh:i=0
         · subst i; simpa only [nearPoint,if_true,basis_eq] using! he
         simpa [M,nearPoint,hh] using! hx
       change Tendsto (fun j=>(b j)⁻¹*((0:Cover) i:ℝ)) _ (𝓝 (q 1 i)); simp only [q,UVNext.FreeStress.camera_zero]; simpa using (tendsto_const_nhds (x:=(0:ℝ)))
    have hr (u:Fin 2): Tendsto (fun j=> M j u) atTop (𝓝 (q u)):= (PiLp.continuous_toLp 2 (fun _ : Axis=>ℝ)).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (show ∀ i:Axis,Tendsto (fun j=> (WithLp.ofLp (M j u)) i) atTop (𝓝 ((WithLp.ofLp (q u)) i)) from hp u))
    exact (PiLp.continuous_toLp 2 (fun i:Fin 2=> E4)).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (show ∀ i:Fin 2,Tendsto (fun j=> (WithLp.ofLp (M j)) i) atTop (𝓝 ((WithLp.ofLp q) i)) from hr))

set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "V!"=> C.labels.level 5
variable {F:Extraction.Order}{𝓛:Ultrafilter (ℕ×ℕ)}{S:Table C.book}
local notation "b!"=> (𝓛:Filter (ℕ×ℕ))
variable {X:Scaling S}{V:∀ i,Vane C i}{Y:∀ d i:ℕ,(Cells.standard C).Field d →L[ℂ] C.label d}
variable {H:(Cells.standard C).Hierarchy}(hq:Gondola F H X 𝓛 V Y)
variable (h:G.Simple)(hb:(𝓛:Filter (ℕ×ℕ)) ≤ F.fuse) (P:F.PointLimits C S)

def b_zoom (V:∀ i,Vane C i)(i:ℕ):= mag C.path.levels (V i|>.b) (V i|>.k)
include h hq
lemma grow_big : Tendsto (b_zoom V) atTop atTop:=by
    have hx:= (mag_rate (b:=5) (A) h (by norm_num)).comp hq.growth;
    exact tendsto_atTop_mono (fun i=> Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (sq_nonneg _)) ((hq.season i).1.high.1.le)) hx
omit h hq
lemma shine (i:ℕ):0<b_zoom V i:= mag_pos ..
def beaconV(i:ℕ)(V:∀ i,Vane C i):Points 2:= Extraction.tag (b_zoom V i)⁻¹ (![nearPoint (b_zoom V i),0]:Fin 2→ Cover)
include hq
lemma kamago (i:ℕ): X.r i • beaconV i V= Extraction.tag (C.S.a (V i).k) (![nearPoint (b_zoom V i),0]: Fin 2→ Cover):=by
    let b:= b_zoom V i; have hp:X.r i=C.S.a (V i).k*b:= (hq.season i).2.symm
    rw [hp]; ext1 x; ext1 k; let s:= (![nearPoint (b_zoom V i),0]: Fin 2→ Cover); change C.S.a _ * b * (b⁻¹* (s x k:ℝ))=_*(s x k:ℝ)
    have he:b≠0:=(shine i).ne'; field_simp
omit hq
include hb P
lemma proxi (L:S.Hierarchy)(d k:ℕ)(l: Fin 2→ Cover)(hl: Extraction.tag (C.S.a k) l ∈ generic _) (v:ℕ×ℕ→ C.label 5)(x:ℕ×ℕ→ C.label d)(y:C.label 5)(z:C.label d) (hv:Tendsto v b! (𝓝 y))(hx:Tendsto x b! (𝓝 z)):
    Tendsto (fun i=>C.numeric i.1 i.2 (![⟨5,v i⟩,⟨d,x i⟩] : Fin 2→ C.book.Token) (location C.S k i.1 i.2 ∘ l)) b! (𝓝 (S.useAt S (Extraction.tag (C.S.a k) l) ![⟨5,S.project 5 y⟩,⟨d,S.project d z⟩])):=by
    let a:Caps 2:= ![5,d]; let u(i:ℕ×ℕ):= Fin.cons (α:=fun j:Fin 2=>C.book.Ref (a j)) (v i) (Fin.cases (motive:=fun j:Fin 1=> C.book.Ref (a j.succ)) (x i) (fun j=>j.elim0))
    let U:= Fin.cons (α:=fun j:Fin 2=>C.book.Ref (a j)) y (Fin.cases (motive:=fun j : Fin 1=> C.book.Ref (a j.succ)) z (fun j=>j.elim0)); let Q:= (![⟨5,y⟩,⟨d,z⟩] : Fin 2→ C.book.Token); let t:=Extraction.tag (C.S.a k) l
    have hT:=paid_point (t:=a) u U (tendsto_pi_nhds.mpr (fun i=>by fin_cases i; exacts[hv,hx])) hb P k l hl
    have hz:S.value a t U=S.useAt S t ![⟨5,S.project 5 y⟩,⟨d,S.project d z⟩]:=by
       let Q':= ripped (t:=a) (C:=C) U; rw [show (![⟨5,S.project 5 y⟩,⟨d,S.project d z⟩]:Fin 2→ S.Tag)= S.classTokens ∘ Q' from ?_, S.at_project S L.laws.toSymmetric (fun _=> le_rfl) (generic_conf _ hl)]; rfl
       funext j; fin_cases j <;> rfl
    have hv:= hz ▸ hT; refine Tendsto.congr ?_ hv
    intro i; rw [show ripped (t:=a) (C:=C) (u i)= ![⟨5,v i⟩,⟨d,x i⟩] from funext (fun j=>by fin_cases j <;> rfl)]
end YM.Trace.Terrace
