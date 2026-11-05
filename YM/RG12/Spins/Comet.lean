import YM.RG12.Spins.Ultra
/-! All powers at one chronological step. Exact Stencils proof adapted from Cub.Starlight, now costed differently. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub.Wild
open Function Filter Set Lattice Wilson RG Pressure Precision Labels Source Source.Drops
open Push Push.Local Planned.PrimaryIntegral295 PPX Flutes Place Bazaars Exterior Streets Postcards WardBin.Lies Cabins Bid
open Next Next.Foundations JointLoad JointLoad.Heir Bloch Carrier Next.Free
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {c f:Side} {n j t d:ℕ}
variable {S:StepData c f} {T:Tube G S}{k:ℝ} {F:Labels.Frame G d}
section pose
variable (p:Probe G d)(M:SectionData F)(A:Hol G) (h : M.Sound A) (hp:Bid.pop M)
   (hk:0<k)(hj:4≤ j)(ht:4≤ t)(hd:d≤j)

-- quantify with HEq to avoid patch.cast mismatch.Stamp.Sign formula B.Current.Phase not using Level.Expr.Env.
 -- ambig
include hp h hk hj ht hd
lemma starlight (i:F.Index) (L:Side) (ρ:ℕ):∀ᶠ x:ℝ in atTop,
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S)(P:Flight j t),S.ratio.count=P.L→P.L=L→ HEq T.R.A0 (linesOf P k)→
    ∀ w y,∀ hB:Blend 2 w y, 2*Heir.reach x<c.val →
       let u:=ocean T (presented M (0:Site f) w (Place.copy F i)) x; let V := A.testLinks d 0 (y • p.1)
       let z:= Seal.donne M h hk ht hp P hd hB; ‖((L.val:ℝ)^d) • iteratedDeriv p.2.val (u ∘ (V:ℝ→ Config G c)) 0 - runProbe F p (z.leads L (Place.copy F i))‖ ≤ (x^ρ)⁻¹ :=by
   let n:=p.2.val
   obtain ⟨s,D,hs,hD,H⟩:=Carrier.priced k hk hj ht
   obtain ⟨C,hC,hF⟩:=Tones.columnPrice M hp i (n+1) 0
   obtain ⟨z,hz,hZ⟩:=Ramble.billFor M.stencil p A 2 s D one_le_two hs hD.le -- argument order
   obtain ⟨K,hK,hV⟩:= Flutes.royalty p A _ one_le_two
   choose! E h₁ h₂ using fun r=> Postcards.replicate M.stencil p 2 k one_le_two hk hj ht r
   let a:= ∑ n∈ Finset.range (p.2.val+1), E n; let Q':=(F.grades i).2
   have ha:0 ≤ a:= Finset.sum_nonneg fun i hi=> h₁ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
   let v' := Oval.league n Q' a C
   let b(x:ℝ):= K*(1+4*(Heir.reach x:ℝ))^(d*n)
   let F0 (x:ℝ) := z*(1+b x)*Real.exp (-(s/2)*(Heir.reach x:ℝ))

   have he₀: YM.RG12.Spins.Super F0:= YM.RG12.Spins.shine_gate (half_pos hs) (zero_le_one.trans hK) hz (d*n)
   have hv0:= YM.RG12.Spins.lease ρ v' he₀ Q' n d L
   filter_upwards [hv0] with x hx c f S T P hP hQ hr w y hB hl
   intro u V Z; have hh: Postcards.forecast M.stencil p (linesOf P k) y w = Postcards.forecast M.stencil p T.R.A0 y w:=by
       have he (i:Side)(X:Lines i)(hf:i=P.L) (h:HEq X (linesOf P k)): Postcards.forecast M.stencil p X y w= Postcards.forecast M.stencil p (linesOf P k) y w:=by subst i; rw [eq_of_heq h]
       exact (he _ _ hP hr).symm
   let N':= Postcards.forecast M.stencil p (linesOf P k) y w
   have hf:N' 0=0:=Postcards.forecast_zero ..
   have hδ:= (Postcards.forecast_truth M.stencil p (linesOf P k) y w (Carrier.stored P k hk ht)).contDiffAt (x:=0)
   have hw: T.R.A0.strip s D:=by
       have h {v:Side}(u:Lines v)(hf:v=P.L)(h:HEq u (linesOf P k)): u.strip s D:=by
          subst v; rw [eq_of_heq h]; have he: (linesOf P k).strip s (D/P.L.val):=by simpa [advanceC] using H P [] (by simp)
          exact Work.F08.strip_mono he le_rfl (div_le_self hD.le (Nat.one_le_cast.mpr P.L.property))
       exact h _ hP hr
   let e := Flutes.lode p A c y w (Heir.reach x)
   let f₁ := (earth M.stencil S T.R.A0 ∘ e)
   have hκ : e 0=0:=by
       unfold e Flutes.lode Cabins.patched; ext1 i; unfold Cabins.room; split; · simp [Flutes.fare_zero,Lattice.gauge]
       exact rfl
   obtain ⟨hw',hψ⟩:= hV c (Heir.reach x) _ _ hB
   have hW:Oval.Fuzz 0 p.2.val f₁ N' (F0 x):=by
       unfold N'; rw [hh]; exact hZ c f S _ _ _ _ (b x) _ hB hw (Flutes.cost_curve p A hB _ _ le_rfl hl) hw' hψ
   have he:Oval.Envelope 0 n N' a:= ⟨ha,fun k' hn=> (h₂ k' hn P _ _ hB).trans (Finset.single_le_sum (fun i hi=>h₁ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))⟩
   let g (f:ℝ→Place.Dev M.stencil G):=Tones.tint M i w ∘ f
   have hT:ContDiffAt ℝ (p.2.val:WithTop ℕ∞) f₁ 0:=(earth M.stencil S _).contDiff.contDiffAt.comp _ hw'
   have hp:=Oval.sticker (hδ.of_le le_top) hT hW he (Place.column_smooth ..) (show w∈Ioc (0:ℝ) 1 from ⟨hB.fine,hB.fits⟩) (show Tones.Width (Place.column M i) (n+1) Q' 0 C from ⟨hC,hF⟩) (by change ‖w • N' 0‖ ≤ 0; simp [hf]) (by simp [f₁,hκ])
   have hi: u ∘ V = g f₁:= terra M _ _ hB.fine x A p i
   rw [hi,← hQ]; rw [show runProbe F p (Z.leads P.L _) = _ from Postcards.measured M h _ P k (2:ℝ) y w hk ht hd hB p i]
   rw [← smul_sub,norm_smul,Real.norm_of_nonneg (by positivity)]
   let I:= iteratedFDeriv ℝ n (g f₁) 0 - iteratedFDeriv ℝ n (g N') 0; let y':Fin n→ℝ:= fun _=>1
   have hI:‖I y'‖≤ v'*(1+F0 x)^(Q'+n)*F0 x:=by simpa only [y',v',n,Finset.prod_const_one,mul_one,norm_one] using ((I.le_opNorm y').trans (mul_le_mul_of_nonneg_right (hp.2.2.2 n le_rfl) (show 0≤∏ i : Fin n,‖(1:ℝ)‖ from Finset.prod_nonneg fun _ _=> norm_nonneg _))) -- syntax
   change (P.L.val:ℝ)^d * ‖I y'‖ ≤ (x^ρ)⁻¹; rw [hQ]; exact (mul_le_mul_of_nonneg_left hI (by positivity)).trans hx
end pose
end YM.PhysicalNext.Repeat.Cub.Wild
