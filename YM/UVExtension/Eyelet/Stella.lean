import YM.UVExtension.Eyelet.Cabin
import Mathlib.Analysis.Normed.Operator.Extend
/-! Fixed observer on the COMPLETE record, no aliases. Let it be naturally
 conjugate-linear for bar orientations. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Eyelet
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Next.Foundations Concert BoundedContinuousFunction
open Motion
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{d :ℕ}{F:Frame G d}{H: Hol G}{p: BudgetPoint}{R:Rep G n} {ι:Type}
def gazeH (m:Motion) : ℂ→+*ℂ := if m.2 then starRingEnd ℂ else RingHom.id ℂ
instance (m:Motion): RingHomIsometric (gazeH m):=by unfold gazeH; split <;>infer_instance
instance (m:Motion): RingHomSurjective (gazeH m):=by unfold gazeH; split <;>infer_instance
lemma tintA (m:Motion)(s:ℂ):gazeH m s=Motion.scalar m s:=by unfold gazeH Motion.scalar; split <;> rfl

section feast
variable {A:Type}{C:Type}{E: A→ Type}{T:C→Type} [∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℂ (E i)][∀ i,NormedAddCommGroup (T i)][∀ i,NormedSpace ℂ (T i)] [∀ i,CompleteSpace (T i)]
lemma blouse (m:Motion)(f:A≃ C)(L:(i:A)→ E i →SL[gazeH m] T (f i)){r:ℝ}(_:0 ≤ r)(h:∀ i x,‖L i x‖ ≤ r*‖x‖): ∃ M:lp E 1 →SL[gazeH m] lp T 1, (∀ x i,M x (f i)=L i (x i))∧ ∀ x,‖M x‖≤ r*‖x‖:=by
   let F i:E i→SL[gazeH m] lp T 1 := (lp.singleContinuousLinearMap ℂ T 1 (f i)).comp (L i)
   let M(x:lp E 1):= ∑' i,F i (x i)
   have ho i (x):F i x= lp.single 1 (f i) (L i x):=rfl
   have hP(v:lp E 1):= insured E (fun i x=> F i x) v (u:=r) (fun i=> by rw [ho,lp.norm_single zero_lt_one]; exact h ..)
   let N : lp E 1→ₛₗ[gazeH m] lp T 1 :={
      toFun:=M
      map_add':=fun v w=> by have he i:F i ((v+w) i)=F i (v i)+F i (w i):=map_add (F i) _ _
                             unfold M; simp_rw [he]; exact (hP v).1.2.summable.tsum_add (hP w).1.2.summable
      map_smul':=fun c x=>by have he i:F i ((c • x) i)= gazeH m c • F i (x i):= (F i).map_smul' _ _
                             unfold M; simp_rw [he]; exact (hP x).1.2.summable.tsum_const_smul _ }
   let Q:= N.mkContinuous r (fun x=> (hP x).2); refine ⟨Q,?_,fun x=> (hP x).2⟩
   intro x i; have hp:= (lp.evalCLM ℂ _ 1 (f i)).hasSum (hP x).1.2
   refine hp.tsum_eq.symm.trans ((tsum_eq_single i ?_).trans ?_)
   · intro j hj; change lp.single 1 (f j) (L j (x j)) (f i)=_; simp [Pi.single_eq_of_ne (f.injective.ne hj.symm)]
   exact lp.single_apply_self (E:=T) 1 (f i) (L i (x i))
end feast
variable (m:Motion)
lemma nought : turnSites m.1 (0:Site n) 0=0 :=by change affine m.1 (0:Site n) 0 = 0; simp [affine]
lemma paints (i:Support n): sky m (0:Site n) i=i.image (turnSites m.1 0):= shading _ _ _

def shift (m: Motion) (n:Side): Region n≃Region n:= Equiv.subtypeEquiv (sky m 0) (fun i=>by
    have he:= shading m (0:Site n) i; change 0∈ i ↔ 0∈ sky _ _ _; rw [he]; constructor -- rewrites both; fix
    · intro h; have hx := Finset.mem_image_of_mem (turnSites m.1 (0 : Site n)) h; rw [nought m] at hx; exact hx
    intro h; obtain ⟨j,hj,h⟩:= Finset.mem_image.mp h; exact (turnSites m.1 (0:Site n)).injective ((nought m).trans h.symm)|>.symm ▸ hj)
lemma travelD (i:Region n): (shift m n i).val = sky m 0 i.val:=rfl
variable (H d p)
local notation "TC"=> Local.turnCost p.order p.power
lemma turnBirth (hn:2≤ n.val)(i:Region n)(x:Birth H i p d)(y:ℝ)(hp:p.supBounds 0 i.val x.val y): Credit H (shift m n i) p d (dance m x.val) ∧ p.supBounds 0 (shift m n i).val (dance m x.val) (Local.turnCost p.order p.power*y):=by
    have hx:= recognizes d H i p x; let s:=m.1; let f:= x.val ∘ pull m.1 (0:Site n)
    let i':= shift m n i; have he:i'.val=i.val.image (turnSites m.1 0):=shading ..
    have h: Reads H 0 i.val (0:Label G d) x.val := (reads_null_iff ..).2 ⟨hx.zero,hx.horizons⟩ -- not
    have hV := reads_pull (b:=0) h hx.pose.sites hn s; have h₀: turnSites s (0:Site n) 0=0:= nought m
    simp only [map_zero] at hV; have hg: Reads H 0 i'.val (0: Label G d) f:=by rw [he]; change Reads _ (turnSites s (0:Site n) 0) _ _ _ at hV; rw [h₀] at hV; exact hV
    have hh:p.Regular i'.val f:= he.symm ▸ regular_pull hx.pose s 0
    have hs:p.supBounds 0 i'.val f (Local.turnCost p.order p.power*y):=by rw [he]; have hh:=bound_pull hx.pose hp s 0; rw [h₀] at hh; exact hh
    cases he:m.2
    · rw [show dance m x.val=f from funext fun i=> by simp [dance,Motion.scalar,he];rfl]; exact ⟨⟨hh,((reads_null_iff ..).mp hg).1,((reads_null_iff ..).mp hg).2,_,hs⟩,hs⟩
    rw [show dance m x.val=star f from funext fun i=> by simp [dance,Motion.scalar,he,f]]; have hv:=bound_bar hh hs
    have hX:=reads_bar hg; rw [map_zero] at hX; exact ⟨⟨regular_bar hh,((reads_null_iff ..).mp hX).1, ((reads_null_iff ..).mp hX).2,_,hv⟩,hv⟩

def capt (hn:2≤ n.val)(i:Region n):Birth H i p d→ₛₗ[gazeH m] Birth H (shift m n i) p d where
   toFun x:=⟨dance m x.val,(turnBirth d H p m hn i x _ ((recognizes d H i p x).cost.choose_spec)).1⟩
   map_add' f g:= Subtype.ext (funext fun j=> Motion.scalar_add m _ _)
   map_smul' c f:= Subtype.ext (funext fun j=> by rw [tintA]; exact Motion.scalar_mul m _ _) -- compile simp

lemma soldE (hn:2≤ n.val)(i:Region n) : ∃ (T:Gondola d H i p→SL[gazeH m] Gondola d H (shift m n i) p), (∀ x,T (twig _ x)=twig _ (capt d H p m hn i x))∧ ∀ v,‖T v‖≤ TC * ‖v‖ :=by
    let f:= capt d H p m hn i
    let T: Birth H i p d→ₛₗ[gazeH m] Gondola d H (shift m n i) p:= (twig _).comp f
    let L:= twig (tin d H i p); have hp(x:Birth H i p d): ‖T x‖≤ TC * ‖L x‖:=
      (pays d H (shift m n i) p (f x)).1 (turnBirth d H p m hn i x ‖L x‖ ((pays _ _ _ _ _).2 le_rfl)).2
    exact ⟨T.extendOfNorm L,fun x=> LinearMap.extendOfNorm_eq (steams _) ⟨_,hp⟩ x,LinearMap.norm_extendOfNorm_apply_le (steams _) _ hp⟩
end YM.UVExtension.Eyelet
