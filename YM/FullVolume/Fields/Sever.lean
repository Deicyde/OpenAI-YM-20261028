import YM.FullVolume.Fields.Tarry
import YM.MergeProof.Arbol
import YM.MergeProof.Paddle
/-!
# Inflate all grade-≥2 components at an intermediate rung
Gain in cover length once markers pinned separately. No rounding singleton/factors. Their Vault & Nectar testimony remains literal.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Sever
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open GridApprox.Nil Local Extra.Trajectories Source Extra.Multi MergeProof MergeProof.Accent
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V I:Type}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
variable {F:Config G n→Poly B}{x:Support n}{o: V→Site n}{t:ℝ}[Fintype V]
def brisk (u:ℕ): ℝ:= Real.exp ((u:ℝ)/64)
section post
omit [Fintype V] in
lemma BoneC (h:Borne o x F t) (z:ℂ): Borne o x (z • F) t:=by
   refine ⟨fun U V h' he=>congr_arg (z • ·) (h.home U V h' he),fun g U=>congr_arg (z • ·) (h.turns g U),fun i=>?_, fun U i hi=>?_⟩
   · simp only [Pi.smul_apply,Poly.part_smul]; exact measurable_const.mul (h.me i)
   simp only [Pi.smul_apply,Poly.part_smul,h.scope U i hi,mul_zero]
omit [Fintype V] in
lemma burns (h:Burns o x F t)(z:ℂ):Burns o x (z • F) t:=⟨BoneC h.toBorne z,fun U hu=>h.permits _ (fun h=> hu (by rw [Pi.smul_apply,h,smul_zero])),fun U=>by simp [h.sil U]⟩
omit [Fintype V] in
lemma flow {x:Box n}(h:Flow o x F t)(z:ℂ): Flow o x (z • F) t:=⟨BoneC h.toBorne z,fun U hu=> h.permits _ (fun h=> hu (by rw [Pi.smul_apply,h,smul_zero]))⟩
omit [Fintype V] in
lemma arise (z:ℂ){P:Poly B}(h:rises P): rises (z • P):=fun i hi=> h i (fun hk=> hi (by rw [Poly.part_smul,hk,mul_zero]))
variable {H:Support n→ Config G n→ Poly B}{K:Box n→ Config G n→ Poly B}
omit [Fintype V] in
lemma lit (h:Carton o H K t)(z:ℂ): Carton o (fun i=> z • H i) (fun i=> z • K i) t :=⟨fun i=> ⟨burns (h.exp i|>.1) z,fun U=> arise z ((h.exp i).2 U)⟩,fun i=> ⟨flow (h.flag i|>.1) z,fun U=> arise z ((h.flag i).2 U)⟩⟩
lemma worth {h:ℕ}{Y:I→ Config G n→Poly B}{s:I→Support n} (ht:Drake B h o)(hv:8≤ h)(he:∀ i,Borne o (s i) (Y i) t)(hp:∀ i U,rises (Y i U))(i:I)(hk:Y i≠0): brisk h≤ Real.exp (coverNumber h (s i)):=by
    obtain ⟨u,hu,x,hx⟩:∃ U,Y i U≠0∧ ∃ x,(Y i U).part x ≠ 0 :=by
        obtain ⟨U,hU⟩:= Function.ne_iff.mp hk; refine ⟨U,hU,?_⟩; by_contra! ha; apply hU; exact Marker.Poly.ext (f:=Y i U) (g:=0) fun x=> ha x
    have hp':=hp i u x hx; have hA := Work.I01.answer n V o h hv x.val (ht.spread x hp') hp' (s i) ((he i).place x u hx); have hb: h ≤ 64*coverNumber h (s i):=(Nat.le_mul_of_pos_right _ (Nat.lt_of_lt_of_le zero_lt_two hp')).trans hA
    apply Real.exp_monotone; apply (div_le_iff₀ (by norm_num)).mpr; rw [mul_comm]; exact_mod_cast hb
-- scale price input.E≥ cost. gain2 using support. preserve min 2 exponent unit. hold fixed anchor all-good labels.S. No discount on individual knots.
lemma incur {w:V→ℝ}{h:ℕ}{Y:I→ Config G n→Poly B}{s:I→Support n}[Fintype I]
   (H:Drake B h o)(hr:8≤h)(hp:∀ i,Borne o (s i) (Y i) t)(hv:∀ i U,rises (Y i U)){k b:ℝ}(hx:Towed w s Y h k b)(he:∀ i,0<w i)(z:ℂ)(hf:‖z‖≤ brisk h):Towed w s (fun i=> z • Y i) h (k-2) b:=by
    obtain ⟨f,hfc,hf',hV⟩:=hx; let g i:=if Y i=0 then 0 else ‖z‖*f i; have hg i:0≤g i:=by unfold g; split; rfl; exact mul_nonneg (norm_nonneg _) ((hV i).fares he|>.1)
    refine ⟨g,Summable.of_finite,fun u=> Extra.Multi.Budget.mono (hf' u) (fun i=>?_ ) (fun i=>?_) le_rfl,fun i=>?_⟩
    · split; exact mul_nonneg (hg i) (Real.exp_pos _).le;rfl
    · split_ifs;swap;·rfl
      dsimp only [g]; split
      next heq=> rw [zero_mul]; exact mul_nonneg ((hV i).fares he|>.1) (Real.exp_pos _).le
      next heq=>
       have hh:= hf.trans (worth H hr hp hv i heq); let a:ℝ:=coverNumber h (s i)
       rw [mul_comm ‖z‖, mul_assoc]; refine mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le).trans ?_) ((hV i).fares he|>.1)
       rw [← Real.exp_add]; apply Real.exp_monotone; have hg:0≤a:=Nat.cast_nonneg _; change a+ (k-2)*a ≤ k*a; linarith
    unfold g; split
    next he=> dsimp only; rw [he,smul_zero]; exact ⟨0,le_rfl,fun U i=> (norm_zero (E:=ℂ)).le, by unfold wordsPrice; simp⟩
    obtain ⟨v,hc,Hf,hQ⟩:= hV i; refine ⟨fun i=> ‖z‖*v i,fun i=>mul_nonneg (norm_nonneg _) (hc i), fun U i'=>?_,?_⟩
    · simp only [Pi.smul_apply,Poly.part_smul,norm_mul]; exact mul_le_mul_of_nonneg_left (Hf ..) (norm_nonneg _)
    apply le_trans _ (mul_le_mul_of_nonneg_left hQ (norm_nonneg _)); unfold wordsPrice; rw [mul_sum]; apply le_of_eq; exact Finset.sum_congr rfl fun i _=> mul_left_comm ..
end post
section
-- generic.Loci. Symbol Serv.
variable (A:Rep G n){w:V→ℝ}{e c:ℝ}(φ:V→ Config G n→ℂ)(ψ:V→ Box n→ Config G n→ℂ) {H:Support n→ Config G n→Poly B}{K:Box n→ Config G n→Poly B}
lemma garnish (hs:8≤ A.p.B)(hp: Carton o H K A.p.threshold)(he:Towed w id H A.p.B e c)(hf:Towed w Prod.fst K A.p.B e c)(hw:∀ i,0<w i)(h:Drake B A.p.B o)(z:ℂ)(hx:‖z‖ ≤ brisk A.p.B): Served A φ ψ (restore A φ ψ (z • H) (z • K)) o w (e-2) c :=by
    exact ⟨z • H,z • K,lit hp z,incur h hs (fun i=>(hp.exp _).1.toBorne) (fun i=>(hp.exp _).2) he hw z hx,incur h hs (fun i=>(hp.flag _).1.toBorne) (fun i=>(hp.flag _).2) hf hw z hx,rfl⟩
end
end YM.FullVolume.Sever
#print axioms YM.FullVolume.Sever.garnish
