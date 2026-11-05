import YM.FullVolume.Amp.Cot
/-! Composition ℓ¹. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp.Beam
open Filter Function Finset Asymptotics Ray RG Push.AbsoluteSums
open scoped Topology BigOperators NNReal ENNReal ContDiff
variable {X Y I : Type} [NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X][NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y] [NormedAddCommGroup I][NormedSpace ℝ I][CompleteSpace I]
variable {s:ℝ}{n j:ℕ}(P:X [×n]→L[ℝ] Y)
-- induction by uncurries trailing one arm.
lemma knit : ∀ {Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y](P:X [×n]→L[ℝ] Y) (p:Fin n→Beam X),∃ Q:Beam Y,(‖Q‖ ≤ ‖P‖*∏ i, ‖p i‖)∧∀ v:sun, read _ v Q=P (fun i=>read X v (p i)):=by
   induction n with
   | zero=>
     intro Y _ _ _ P p; refine ⟨arm (P 0),?_ ,fun v=> Eq.trans (armL ..) (congr_arg P (Subsingleton.elim _ _))⟩; rw [armN]; simpa using P.le_opNorm 0
   | succ n ih=>
     intro Y _ _ _ P p; obtain ⟨Q,hQ,h⟩:= ih P.curryRight (Fin.init p) -- curry strong
     let a:=p (Fin.last n)
     let f:= (ContinuousLinearMap.id ℝ (X→L[ℝ] Y)) -- operator Bilinear
     refine ⟨brave f Q a, (braveN f Q a).trans ?_,?_⟩
     · rw [Fin.prod_univ_castSucc]; let v:=∏ i:Fin n,‖(Fin.init p) i‖
       have hv:=ContinuousLinearMap.norm_id_le (𝕜:=ℝ) (E:= (X→L[ℝ] Y)); rw [ContinuousMultilinearMap.curryRight_norm] at hQ
       apply (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hv).trans; apply (mul_le_mul_of_nonneg_right hQ (norm_nonneg _)).trans_eq; rw [mul_assoc]; rfl
     intro v; rw [harp, h v]; let g i:=read X v (p i); change P.curryRight (Fin.init g) (g (Fin.last n))=P g; simp
-- lift as ML
lemma knitted : ∃ R:(Beam X) [×n]→L[ℝ] (Beam Y), ‖R‖≤‖P‖∧∀ v:sun,∀ u:Fin n→Beam X, read _ v (R u)=P (fun i=>read X v (u i)):=by
   choose P' hP hX using knit P
   let V (U:Fin n→Beam X) (s:sun)(i:Fin n):= read X s (U i)
   have ht (v:Fin n→ Beam X) (i:Fin n)(x:Beam X)(s:sun): V (Function.update v i x) s=Function.update (V v s) i (read _ s x):=by
      unfold V; funext j; by_cases hp:j=i
      · subst j; simp
      simp [hp]
   let f: MultilinearMap ℝ (fun _:Fin n=>Beam X) (Beam Y):={ toFun:=P',
                                                              map_update_add' := by
                                                                  intro H; cases Subsingleton.elim H (instDecidableEqFin n); intro u i a b; refine soul _ _ (fun v=>?_); change read Y v (P' _)=read Y v (P' _+P' _); rw [map_add,hX,hX,hX]; change P (V _ v)=P (V _ v)+P (V _ v); rw [ht,ht,ht,map_add,ContinuousMultilinearMap.map_update_add],
                                                              map_update_smul' := by
                                                                  intro H; cases Subsingleton.elim H (instDecidableEqFin n); intro u i a b; apply soul; intro v; change read Y v (P' _)=read Y v (a • P' _); rw [map_smul,hX,hX]; change P (V _ v)=a • P (V _ v); rw [ht,ht,map_smul,ContinuousMultilinearMap.map_update_smul] }
   exact ⟨f.mkContinuous ‖P‖ hP,f.mkContinuous_norm_le (norm_nonneg _) hP,fun v u=>hX u v⟩
variable (K:FormalMultilinearSeries ℝ X Y) (x:Beam X)
def stitch (n:ℕ):= (knitted (K n)).choose
lemma beads (v:sun): read Y v (stitch K n (fun _=>x))= K n (fun _=> read X v x):= (knitted _).choose_spec.2 v _
lemma stitchN : ‖stitch K n‖ ≤ ‖K n‖:= (knitted _).choose_spec.1
def ride (n:ℕ):= stitch K (n+1) (fun _=>x)
def showB : Beam Y:=∑' n,ride K x n
-- shrink. norms coeff ≤(1/α)^n*c, work α≥1. .1/4 factor. price via elementary.
variable {c p r:ℝ} (hp:0≤p)(hc:∀ n, ‖K n‖ ≤ p^n*c)(hx:‖x‖≤r)(ht:p*r ≤ 1/4)
include hp hc hx ht
lemma ridge (n:ℕ): ‖ride K x n‖≤ (1/4:ℝ)^n * (p*r*c):=by
   have hu:0≤r:= (norm_nonneg _).trans hx; have hL:0 ≤c:= by have h:=hc 0; simp at h; exact (norm_nonneg _).trans h
   have h:=ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (stitchN K |>.trans (hc (n+1))) (fun _:Fin (n+1)=>hx)
   unfold ride; simp only [prod_const,Finset.card_univ,Fintype.card_fin] at h
   exact h.trans ((show _ = (p*r)^n*(p*r*c) from (by simp_rw [pow_succ,mul_pow]; ring)).trans_le (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ht _) (by positivity)))
lemma ribs: SumBudget (fun i=> ‖ride K x i‖) (p*r*c*2):= by
   have hh:= ridge K x hp hc hx ht; have hnn:0 ≤ p*r*c:=by have h:=hh 0; simp at h; exact (norm_nonneg _).trans h
   apply budget_loosen (budget_mono (budget_geometric (q:=(1/4:ℝ)) hnn (by norm_num) (by norm_num)) (fun _=>norm_nonneg _) (fun i=>mul_comm _ (p*r*c) ▸ hh i))
   exact mul_le_mul_of_nonneg_left (by norm_num) hnn
lemma showN: ‖showB K x‖≤ p*r*c*2:= let h:=ribs K x hp hc hx ht; (norm_tsum_le_tsum_norm h.2.1).trans h.2.2
lemma showL (v:sun): read Y v (showB K x)=∑' n:ℕ, K (n+1) (fun _=>read X v x):=by
   have he:=(read Y v).hasSum (ribs K x hp hc hx ht).2.1.of_norm.hasSum; unfold ride at he; simp_rw [beads] at he; exact he.tsum_eq.symm
-- Lipschitz κ factor
variable (y:Beam X)(hy:‖y‖≤r)
include y hy
lemma lemmaD (n:ℕ): ‖ride K x n- ride K y n‖≤ p*c*‖x-y‖*(1/2:ℝ)^n:=by
   have hu:0≤r:= (norm_nonneg _).trans hx; have h:= (stitch K (n+1)).norm_image_sub_le (fun _=>x) (fun _=>y); rw [show ((fun _:Fin (n+1)=>x)-(fun _=>y))=fun _=>x-y from rfl] at h
   simp at h
   have hg(n:ℕ): ((n:ℝ)+1) ≤ 2^n:=by
     induction n with
     | zero=>simp
     | succ k ih=>push_cast; rw [pow_succ]; linarith [show 0≤(k:ℝ) by positivity]
   refine h.trans ?_
   have hc':= stitchN (n:=n+1) K
   have hL:0 ≤c:= by have h:=hc 0; simp at h; exact (norm_nonneg _).trans h
   calc
     _ ≤ (p^(n+1)*c)*2^n*r^n*‖x-y‖:= mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul (hc'.trans (hc _)) (hg n) (by positivity) (by positivity)) (pow_le_pow_left₀ ((norm_nonneg _).trans (le_max_left ..)) (max_le hx hy) _) (by positivity) (by positivity)) (norm_nonneg _)
     _ = p*c*‖x-y‖*((p*r)*2)^n:=by simp [mul_pow,pow_succ]; ring
     _ ≤ _:= mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity)
lemma showD : ‖showB K x-showB K y‖ ≤ 2*p*c*‖x-y‖:=by
  have hL:0 ≤c:= by have h:=hc 0; simp at h; exact (norm_nonneg _).trans h
  have he:= (ribs K x hp hc hx ht).2.1.of_norm.hasSum.sub (ribs K y hp hc hy ht).2.1.of_norm.hasSum; let a:=p*c*‖x-y‖; have ha:0≤a:=by unfold a; positivity
  have hh:=budget_mono (budget_geometric (q:=(1/2:ℝ)) ha (by norm_num) (by norm_num)) (fun i=>norm_nonneg (ride K x i-ride K y i)) (lemmaD K x hp hc hx ht y hy)
  change ‖_‖≤_*‖x-y‖; unfold showB; rw [← he.tsum_eq]; exact (norm_tsum_le_tsum_norm hh.2.1).trans (hh.2.2.trans_eq (by unfold a; ring))
end YM.FullVolume.Amp.Beam
