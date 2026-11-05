import YM.TraceExtension.Shelves.Inca
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shelves
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Perfect Turret Margin Slate Next.UVStress
open ProofPorts.GridRealModelsEstimates20261012
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}(I:Watch C) (k N p d:ℕ)
set_option quotPrecheck false
local notation "n"=> C.side k p
local notation "T"=> C.path
open Finset
variable {k N p d}
lemma fade_ss (F:Peat G (C.side k p))(hp:Envelope (filmR F))(v:ℝ): Envelope (filmR (v • F)):=by rw [coatsS (p:=p) (k:=k) (C:=C)]; exact (Envelope.constC _).mulC hp
lemma fade_i (F:Peat G (C.side k p))(hp:Envelope (filmR F))(j:Site (C.side k p)): Envelope (filmR (rj j F)):=by rw[CoatShift (C:=C)];exact hp.comp_env ((show Continuous (fun U:Config G (C.side k p)=> Lattice.translate j U) from by unfold Lattice.translate; fun_prop).measurable)
lemma fade_m(f g:Peat G (C.side k p))(hx:Envelope (filmR f))(hp:Envelope (filmR g)): Envelope (filmR (f - g))∧ (∀ h:k ≤ N,∀ u:Cover,Fold I k N p d (f-g) u=Fold I k N p d f u-Fold I k N p d g u):=by
    have he:=fade_ss g hp (-1); rw[neg_one_smul] at he; constructor
    · rw[(Shunt.plush ∅ _ _ (C.path.rep N p k) 0).2.2]; exact hx.subC hp
    intro h u; rw[sub_eq_add_neg,Fold_add I u h hx he,← neg_one_smul ℝ g,book_s I _ u h g, neg_one_smul];rfl
lemma fade_w {V:Type}(P:V→ Peat G (C.side k p))(s:Finset V)(he:∀ i∈s,Envelope (filmR (P i))): Envelope (filmR (∑ i∈s,P i))∧ (∀ h:k≤ N,∀ u:Cover,Fold I k N p d (∑ i∈s,P i) u=∑ i∈s,Fold I k N p d (P i) u):=by
   induction s using Finset.induction_on with
   | empty=>simp only [sum_empty]; exact ⟨(show Envelope (filmR (0:Peat G (C.side k p))) from by rw [show filmR (0:Peat G n)=0 from (coatsS (C:=C) (k:=k) (p:=p) 0 0|>fun h=> by simpa only [zero_smul, Complex.ofReal_zero] using h)]; exact Envelope.constC (0:ℂ)), fun h u=>Fold_null I u h⟩
   | insert i s hi ih=>
      obtain ⟨hx,hP⟩:= ih (fun i h=> he i (mem_insert_of_mem h)); simp only[sum_insert hi]; let f:=P i; have hg := he i (mem_insert_self i s); refine ⟨?_,fun h u=>?_⟩
      · rw[(Shunt.plush ∅ _ _ (C.path.rep N p k) 0).1]; exact hg.addC hx
      rw[Fold_add I u h hg hx,hP h]
-- dimension shift
lemma accol (C:Family G)(k d:ℕ): alto C.path k (d+1)=(↑(C.S.a k)⁻¹:ℂ)*alto C.path k d:=by unfold alto; change ( (↑(C.S.a k):ℂ)^(d+1))⁻¹=_; rw [pow_succ,mul_inv_rev,Complex.ofReal_inv]
lemma Fold_more(Z: Peat G (C.side k p))(d:ℕ)(h:k≤ N)(l:Cover): Fold I k N p (d+1) Z l= (C.S.a k)⁻¹ • Fold I k N p d Z l:=by
    unfold Fold; simp only[dif_pos h]; rw[accol C k d,mul_smul,backTo_linear (C:=C)]; change _= ((C.S.a k)⁻¹) • _; unfold moment; simp only [Pi.smul_apply,smul_eq_mul, Complex.real_smul, mul_assoc,integral_const_mul, Complex.ofReal_inv]
lemma beacon_h (d:ℕ)(f:CrG G (C.side k p))(h:k ≤ N)(hv:Bounce f)(hq:Envelope (filmR (f 0)))(i:Axis)(l:ℤ):
    let Z := fun y:ℤ=> Fold I k N p d (f 0) (y • step i)
    Fold I k N p (d+1) (twig i f 0) (l • step i)= (C.S.a k)⁻¹ • (Z (l+1)- Z l) ∧ Fold I k N p (d+1) (elm i f 0) (l • step i)=(C.S.a k)⁻¹ • dTap Z l:=by
    intro Z; let a:=(l • step i: Cover); let K(g:Peat G (C.side k p)):= Fold I k N p d g a; let F(r:ℤ):= f (0+r • step i); have hx(r:ℤ): f (0+r • step i)=rj (wrap (C.side k p) (r • step i)) (f 0):=by rw [map_zsmul,wrap_step,zero_add]; exact (hv.trap _).symm
    have hF(r:ℤ): Envelope (filmR (F r)):= by unfold F; rw [hx]; exact fade_i _ hq _
    have he(u):K (F u)= Z (l+u):=by unfold K F; rw [hx,Fold_step I _ _ h hq]; unfold Z; rw [add_smul]
    rw [Fold_more I _ d h,Fold_more I _ d h]; constructor <;> apply congr_arg
    · unfold twig; rw[show f (0+step i)=F 1 from (by unfold F; rw [one_smul])]; change K _=_; rw [show K _=_ from (fade_m I (F 1) (f 0) (hF 1) hq|>.2 h a), ←he]
    let w(j:Fin 4):=0+(steps j:ℤ); let v(j:Fin 4):=0-(steps j:ℤ); let f(j:Fin 4):= cash j • (F (w j)-F (v j));change Fold I k N p d (∑ j,f j) a= _
    rw [(fade_w I f univ (fun j _=> fade_ss _ ((fade_m I (F (w j)) _ (hF _) (hF (v j)) (d:=d) (N:=N)).1) _) (d:=d) (N:=N)).2 h]; unfold dTap; refine sum_congr rfl (fun j _=>?_); unfold f; rw [book_s I (d:=d) _ a h, (fade_m I (F (w j)) _ (hF _) (hF (v j)) (d:=d) (N:=N)).2 h a]; change cash j • (K _-K _)= _; rw[he,he]; unfold w v;simp [sub_eq_add_neg]
end YM.Trace.Shelves
