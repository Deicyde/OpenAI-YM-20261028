import YM.OPE.Interpolate.Corridor
import YM.OPE.Schemes.Ladder

/-!
# Updating an observation near a collapsing configuration family
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Set Word Lattice RG Wilson MergeProof Ribbons Accent Source PhysicalNext.Repeat.Legato Next.Extract Next.UVStress Bid
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S){I J L : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{φ:Filter L}[φ.NeBot] {T : L→ℝ} {x v u a b c d y z : ℝ} {k m j: L→ℕ} (g:I→ C.book.Token) (r:J→ C.book.Token) {X:L→ I→ E4}{Y:L→J→ E4} {q q':ℕ}
    {P:L→ C.label q}
variable {M} {E : Dash.Bin M} {t} {H} (Base' : Base C F M t E S H)
set_option quotPrecheck false
local notation "Λ" => U.sector.derivatives
variable {R: Prescription U.sector.derivatives}(w : Mode U.sector.derivatives)
variable (hT:Tendsto T φ atTop)(hx:Corridor φ T x X)(ha:0<x)

structure Cadet {G:Gauge} {L:Register G} {S:Table L}(P:DiffPlan S)(f:(I→L.Token)→(I→E4)→ℂ)(x:I→ E4) (v:I→ L.Token) : Prop where
   works : DifferentiableAt ℝ (f v) x
   slopes (i:I)(a:Axis) : fderiv ℝ (f v) x (kindle i a) = f (touched v i a P) x

variable {G':Gauge}{R':Register G'}{S':Table R'}{P':DiffPlan S'}{f f':(I→R'.Token)→(I→E4)→ℂ}{x':I→ E4}{v':I→R'.Token}
lemma Cadet.observe (A:Table R')(h:A.Hierarchy)(hs:P'.Derivatives A)(hr:A.respects S'){y:J→ E4}(z:J→R'.Token)(hx:Injective (beside x' y)) : Cadet P' (fun x v=> OPE.observe A (beside v y) (beside x z)) x' v':=
    ⟨(under_read A v' z P' h hs hr hx).1,(under_read A v' z P' h hs hr hx).2⟩
lemma Cadet.reading (i:Exterior R')(hp:S'.Hierarchy)(h:P'.Derivatives S')(he:Injective (beside x' (bearing i))) : Cadet P' (fun p x=> Prescription.reading S' x p 0 i) x' v' :=by
    let f p (x:I→E4):= Prescription.reading S' x p 0 i; let g p (x:I→E4):= OPE.observe S' (beside x (bearing i)) (beside p i.letter); have hc : Cadet P' g x' v':= Cadet.observe _ hp h (fun _=>le_rfl) _ he
    have hg(p): f p=ᶠ[𝓝 x'] g p:=by
       have hz := ((beside_derive (x:=x') (y:=bearing i)).continuousAt.tendsto).eventually (show ∀ᶠ y:I⊕Fin i.n → E4 in 𝓝 (beside x' (bearing i)), Injective y from open_inj.mem_nhds he)
       filter_upwards [hz] with i' hi; unfold f g; simp only [Prescription.reading,sub_zero, if_pos hi]
    refine ⟨hc.works.congr_of_eventuallyEq (hg v'),fun i a => Eq.trans (congr_arg (fun p:(I→E4)→L[ℝ] ℂ=> p (kindle i a)) (hg v'|>.fderiv_eq)) ?_⟩
    exact (hc.slopes i a).trans (hg (touched v' i a P')|>.eq_of_nhds).symm
lemma Cadet.scaled (h:Cadet P' f x' v')(u:ℂ) : Cadet P' (fun p x=>u*f p x) x' v':=by
    exact ⟨h.works.const_mul u,fun i a=>by change fderiv ℝ (u • f v') _ _=_; rw [(h.works.hasFDerivAt.const_smul u).fderiv]; simp [h.slopes]⟩ -- defeq smul
lemma Cadet.spanned (h:Cadet P' f x' v')(u:ℂ): Cadet P' (fun p x=> f p x*u) x' v':=by simpa only [mul_comm u] using h.scaled u
lemma Cadet.sub (h:Cadet P' f x' v')(he:Cadet P' f' x' v'): Cadet P' (fun p x=> f p x-f' p x) x' v':=by exact ⟨(h.works.sub he.works),fun i a=>by rw [fderiv_fun_sub h.works he.works]; simp [h.slopes,he.slopes]⟩
lemma Cadet.list {J:Type}(U:J→(I→R'.Token)→(I→E4)→ℂ){B:Finset J}(h: ∀ i∈ B,Cadet P' (U i) x' v'): Cadet P' (fun p x=>∑ i∈B,U i p x) x' v':=by
    refine ⟨(HasFDerivAt.fun_sum (fun i hi=> (h i hi).works.hasFDerivAt)).differentiableAt,fun i a=>?_⟩
    rw [fderiv_fun_sum (fun i hi=> (h i hi).works)]; simp only [_root_.sum_apply]; exact Finset.sum_congr rfl fun j hi=> (h j hi).slopes i a
include U hx ha hT
lemma cadence_coeff : ∀ᶠ i in φ, Cadet Λ (fun v x=> R.ope w x v 0) (X i) g:=by
    filter_upwards [(eventually_all_finset (R.sheet w).support).2 fun i hi=> epoch_space hT hx.managed hx.room ha i] with i hi
    exact Cadet.list (fun (i:Exterior C.book)(v:I→C.book.Token)(x:I→ E4)=>(R.sheet w) i*Prescription.reading S x v 0 i) (B:=(R.sheet w).support) (fun x hx=> (Cadet.reading x U.room.kernel U.phase.transport.derivatives (hi x hx)).scaled _)
local notation "z0"=> (fun i:L=> sole (0:E4))
variable (s:L→Viewers U)(hp: Intervals φ T a (centerless L) Y)(hg: Kept φ T b Y)(he:a<x)
local notation "θ"=> (fun i=>spectator U (s i))
local notation "Ω"=> (fun i v x=> observe (θ i) (beside x (Y i)) (beside v r))
include hp hg he
lemma cadence_total (N:ℕ): ∀ᶠ i in φ, Cadet Λ (fun v x=> Ω i v x - R.truncated (θ i) N x v 0 (Y i) r) (X i) g:=by
    have hh := director_space hT hx.room hp he; have hV:= ((hx.managed.mono (le_max_left x b)).chorus (hg.mono (le_max_right ..)) (hh.mono (he.le.trans (le_max_left ..)))).inject
    filter_upwards [(eventually_all_finset (bands Λ N)).2 fun i hi=> cadence_coeff (R:=R) U g i hT hx ha,hV] with i hi h
    exact (Cadet.observe _ (spectate U (s i)) (spectate_evolution U _) (spectate_respects U _) r h).sub (Cadet.list (fun j v x=> R.termRead (θ i) x v 0 j (Y i) r) (B:=bands Λ N) (fun j hj=>(hi j hj).spanned _))
end YM.OPE
