import YM.RG05Readout.Offsets.Rows
/-!
# Shortening field horizon while retaining the test exponent

Here the reading of jets truncates on monomials in field position weight (not
slot degree or jet-variable count). The horizon conversion in scalar outputs
sustains this read. On wrapping roots the test still retains ALL address
placement in the external azimuth. No translated-projection assertions here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set Lattice Wilson Labels RG Source Extra.Histories Push Local
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G: Gauge}{n:Side}{d e k:ℕ} (T:Labels.Frame G e) (F:Labels.Frame G d)
open Next.Foundations Drops
-- Trim the field test directions physically: exact even before taking germ.
def reduced (e:ℕ)(J:Jet G):= Drops.expand e (Drops.trunk e J)
lemma potential_prune (h:e ≤ d) (J:Jet G) : Source.potential d (reduced e J) = Source.potential e J:=by
    rw [← Drops.truncate (d:=e) J]; unfold reduced
    funext i x; unfold potential; symm
    refine Finset.sum_subset (fun j hj=> Finset.mem_range.mpr ?_) ?_
    · apply lt_of_lt_of_le (Finset.mem_range.mp hj); omega
    intro j _ hz; rw [Drops.expand,dif_neg (mt Finset.mem_range.mpr hz)];rfl
lemma prune_test (A:Hol G) (h:e≤d)(o:Site n) (z : Jet G) : A.testLinks d o (reduced e z)= A.testLinks e o z:=by
    funext t j; let W:Edge Cover:= (lift (j.1-o),j.2)
    have hz:= A.solves d (reduced e z) t W
    have he : partConnection d (reduced e z) t W=partConnection e z t W:=by unfold partConnection;rw [potential_prune h]
    rw [he] at hz; exact congr_fun (hz.unique (A.solves ..)) _
lemma prune_smul (a:ℝ) (J:Jet G) : reduced e (a • J)=a • reduced e J:=by
    funext i; unfold reduced Drops.expand; rw [Pi.smul_apply]; split_ifs with hi
    · rfl
    simp
lemma prune_vanish {A:Hol G}{X:Config G n→ℂ}{o:Site n} (h:e≤d) (hf:A.PiVanish d o X):A.PiVanish e o X:=by
    intro J; let Y:= reduced e J; obtain ⟨hq,hδ⟩:=hf Y
    rw [prune_test A h] at hq hδ -- Y
    exact ⟨hq.of_le (Nat.cast_le.mpr h),fun i hi=>hδ _ (hi.trans h)⟩
lemma horizon_cost_price : ∃ C>0,∀ (h:e≤d){k:ℕ} (x:T.Coeff)(y:F.Coeff),
    (∀ (J:Probe G e), runProbe T J x=runProbe F (reduced e J.1,⟨J.2.val,Nat.add_le_add_right h 1|>.trans_lt' J.2.isLt⟩) y) → T.coeffSize (Offsets.basisCut T k x)≤ C*F.coeffSize (Offsets.basisCut F k y):=by
    by_cases hp:e≤d
    · let U (J:Probe G e):Probe G d:=⟨reduced e J.1,⟨J.2.val,lt_of_lt_of_le J.2.isLt (Nat.add_le_add_right hp 1)⟩⟩
      obtain ⟨V,c,h₁,hσ⟩:=probe_budget T; let r:=1+∑ i∈ V,‖runProbe F (U i)‖
      have hz:= Finset.sum_nonneg (s:=V) (f:=fun i=>‖runProbe F (U i)‖) (fun _ _=>norm_nonneg _); have hr:0<r:=by unfold r; linarith
      refine ⟨c*r,mul_pos (zero_lt_one.trans_le h₁) hr,fun h k x y hf=>?_⟩; rw [mul_assoc]
      apply hσ _ _ (mul_nonneg hr.le (Work.G08.size_nonneg ..)) (fun i hi=> ?_)
      rw [show runProbe T i (Offsets.basisCut T k x)=runProbe F (U i) (Offsets.basisCut F k y) from by rw [Offsets.projected,Offsets.projected,hf]]
      apply ((runProbe F (U i)).le_opNorm _).trans
      apply mul_le_mul _ (norm_le_size ..) (norm_nonneg _) hr.le
      exact (Finset.single_le_sum (fun i _=> norm_nonneg (runProbe F (U i))) hi).trans (le_add_of_nonneg_left zero_le_one)
    exact ⟨1,zero_lt_one,fun h=>(hp h).elim⟩
lemma axis_cost (i:F.Index)(z:ℂ): F.coeffSize (z • (Frame.coords F (F.basis i))) = ‖z‖ := by
    rw [Frame.coords_basis,Frame.coeffSize, Finset.sum_eq_single i]; simp; intro j _ hj; simp [hj]; simp
end YM.RG05Readout.Address
