import YM.TraceExtension.Pills.Ames
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pills
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{I:Type}
abbrev beltM(a:Wo G)(s:Seat n):= s.spread (a.footprint 0)
lemma sweetW (p:Wo G)(s:Seat n): Drift _ (miniC p s):= fun X _ _ U x h=>contDiffAt_const.mul (spunok s p _ X _ _ h)
lemma homex (p:Wo G)(hp:p.Invariant)(s:Seat n)(hG:G.Simple): GaugeInvariant (miniC p s) ∧ miniC p s∈loom G n:=by
   have he: GaugeInvariant (miniC p s):=by intro W U; simp only [miniC,Seat.view,Push.Local.pull_gauge,Atom.unmasked,Work.F05.slot_gauge]; exact congr_arg (_*·) (hp ..)
   refine ⟨he,clergyP _ he (sweetW p s _ _ _ (Army.powL (v:=id) contDiffAt_id)) ?_ hG⟩
   unfold miniC; rw [show s.view (1:Config G n)=1 from ?_]; swap; · change pull _ _ (1:Config G n)=_; funext i; unfold pull Step.read; split; exact _root_.inv_one; rfl
   have hp(i:RG.Slot): i.atSite (1:Config G n) 0=0:=by rw[Work.F03.atSite_path, WilsonStartup.face_one,G.curvature_unit,map_zero]
   simp[Atom.unmasked,Atom.poly,hp]
lemma reach_h (p:Wo G)(s:Seat n): LocalOn (beltM p s) (miniC p s):=fun U V h=> congr_arg (_*·) (strong_move (Derivs.atom_local p 0) s U V h)
private lemma hull_bound (p:Wo G)(s:Seat n): beltM p s⊆ sprout s.2 p.length:=by
    intro x hx; obtain ⟨y,hy,rfl⟩:= mem_image.mp hx
    have he:separation (0:Site n) y≤ p.length:=by
       obtain ⟨q,hq,rfl⟩:=mem_image.mp hy; rcases mem_insert.mp hq with h|h; · rw[h];simp
       obtain ⟨i,_,hh⟩:= mem_biUnion.mp h
       rw [separation_comm]; apply (VerifiedReset.slot_length (p.leg i) (0:Site n) (y:=wrap n q+0) (mem_image_of_mem _ hh)).trans (single_le_sum (f:=fun i=> (p.leg i).length) (fun j _=> Nat.zero_le _) (mem_univ i))
    apply halo_spec.mpr ⟨s.2,mem_singleton_self _,?_⟩; apply le_trans ?_ he; exact (show separation (affine s.1 s.2 (0:Site n)) (affine s.1 s.2 y)= separation 0 y from Push.Local.turn_sep s.1 s.2 _ _) ▸ (by rw [show affine s.1 s.2 (0:Site n)=s.2 from by simp[affine]])
section
variable (x:Site n)(r t:ℕ) (P:I→Wo G)(L: Finset I)
def OΩ:= (univ:Finset Signed) ×ˢ (sprout x (t+r))
def prunedX: Peat G n:=∑ i∈L,∑ s∈OΩ x r t,miniC (P i) s
variable {x r t}
private lemma sol(i:I)(s:Seat n)(U:Config G n): DifferentiableAt ℝ (fun x=> miniC (P i) s (input G n x*U)) 0:=(sweetW (P i) s _ _ _ ((Army.powL (v:=id) contDiffAt_id).mul (Army.park U _))).differentiableAt (by simp)
lemma halo_eq {Y:Gal G n}(hy:Clouded Y (sprout x r))(h:∀ i∈L,(P i).length ≤ t): rill (prunedX x r t P L) Y = rill (paper L P) Y:=by
    ext1 U; rw[hail,hail,paper_at]; apply sum_congr rfl fun e _=> ?_ ; by_cases hv:e.1∈sprout x r
    · apply congr_arg; unfold outD prunedX; simp only[Finset.sum_apply]
      have hx(M:Finset (Seat n)):
         fderiv ℝ (fun v=>∑ i∈L,∑ s∈M,miniC (P i) s (input G n v*U)) 0 (bolt e)=∑ i∈L,∑ s∈M,outD (miniC (P i) s) e U:=by
          rw[fderiv_fun_sum]; rw[_root_.sum_apply]; apply sum_congr rfl fun i _=>?_ ; rw[fderiv_fun_sum (fun j _=>sol P i j U), _root_.sum_apply];rfl
          intro i _; exact DifferentiableAt.fun_sum (fun k _=> sol P i k _)
      rw[hx,hx]; apply sum_congr rfl fun i hi=>?_ ; apply sum_subset (Finset.subset_univ _) fun s _ hp=>?_ ; apply out_home e (sol _ ..) _ (reach_h (P i) s)
      intro hl; apply hp; obtain ⟨v,hv,hx⟩:=halo_spec.mp hv; obtain ⟨b,hb,he⟩:=halo_spec.mp (hull_bound (P i) s hl); refine mem_product.mpr ⟨mem_univ _,halo_spec.mpr ⟨v,hv,?_⟩⟩; rw [mem_singleton.mp hb,separation_comm] at he; exact (separation_triangle v _ _).trans ((Nat.add_le_add hx (he.trans (h i hi))).trans_eq (add_comm ..))
    rw [hy.toes _ _ hv,zero_mul,zero_mul]
lemma drip : Drift _ (prunedX x r t P L):=by
    intro X _ _ U v H; unfold Function.comp; simp only [prunedX,Finset.sum_apply]; exact ContDiffAt.sum (fun i hi=> ContDiffAt.sum fun s _=> sweetW _ _ X U v H)
end
lemma paid_h (G:Gauge)(A:ℝ)(hA:0 ≤ A) (k t:ℕ): ∃ D:ℝ,0≤ D ∧ ∀ (I:Type)(n:Side)(v:I→Wo G)(L: Finset I), G.Simple→ (∀ i∈L,(v i).Invariant)→ (∀ i∈L,(v i).length≤ t)→∀ (C:ℝ),(∑ i∈L,(v i).magnitude)≤ C →∀ (r:ℕ)(x:Site n),
    Splendor (prunedX x r t v L) (sprout x (t+(t+r))) k (C*D*↑(((t+r+(t+r)+1)^4):ℕ)) A:=by
    obtain ⟨F,⟨hf,S,p,hS,hF⟩,H⟩:= roundBill G A hA k 2; let T:=S*(1+(t:ℝ))^p; let D:= Fintype.card Signed *T; have ht:0 ≤ T:=by unfold T; positivity
    refine ⟨D,by positivity,fun I n v L hG hp hv C h r x=>?_⟩
    let W:=OΩ x r t; let B:= sprout x (t+(t+r)); let c(i:I):= (v i).magnitude; have hc(i):0 ≤ c i:=sum_nonneg fun i _=>abs_nonneg _
    have hx:(W.card:ℝ) ≤ Fintype.card Signed * ↑(((t+r+(t+r)+1)^4):ℕ):=by
        exact_mod_cast (show W.card ≤ Fintype.card Signed * _ from (by unfold W OΩ; rw[card_product,card_univ]; exact Nat.mul_le_mul_left _ (le_trans (Corona.halo_size ..) (by simp))))
    have he(i)(hi:i∈L) (s:Seat n)(hs:s∈W): Splendor (miniC (v i) s) B k (c i*T) A:=by
       obtain ⟨hh,hx⟩:= homex (v i) (hp i hi) s hG; obtain ⟨b,hb,hg⟩:= halo_spec.mp (mem_product.mp hs|>.2); rw[mem_singleton.mp hb] at hg
       have hk:beltM (v i) s⊆ B:= (hull_bound ..).trans ((sprout_mono _ (hv i hi)).trans (hedge hg _))
       refine ⟨hx,fun U V h=> reach_h _ _ U V (agrees_mono h hk),hh,fun U=> sweetW (v i) s _ _ _ (Turret.incrementA U 0),fun X _ _ U x hw=> ?_⟩
       have ht:Allows k (fun y=> (v i).unmasked ((s.view ∘ U) y) 0) x (c i*T):= ((H X n _ _ _ x (rollA s hw)) : Allows k (fun y=> (v i).unmasked ((s.view ∘ U) y) 0) x (c i* F (v i).length)).mono (mul_le_mul_of_nonneg_left ((hF _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by gcongr; exact hv i hi) _ ) (by positivity))) (hc i))
       exact (ht.smul VerifiedReset.factor).mono (mul_le_of_le_one_left ht.nonneg (by rw[abs_of_pos factor_pos]; exact factor_le))
    apply (sparkle _ L _ (fun i hi=>sparkle _ W _ (fun s hs=> he i hi s hs))).up (fun p h=>h); simp only [sum_const,nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    apply le_trans (mul_le_mul hx (mul_le_mul_of_nonneg_right h ht) (mul_nonneg (sum_nonneg fun i _=> hc i) ht) (by positivity)) (le_of_eq ?_); unfold D; ring
end YM.Trace.Pills
