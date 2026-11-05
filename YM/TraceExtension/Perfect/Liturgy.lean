import YM.TraceExtension.Perfect.Eon
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG RG.Supply Wilson Finset Push.Uniform Planned.PrimaryIntegral295 Next.Free
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical

variable {G:Gauge}{s:Stage}
-- retain stage plan across Bolt.A.
abbrev Ember (a:Levels G)(m:ℕ): Type:= Eon G (a.params (m+1)) a.clock.kernel (a.clock.op m 0).patch (a.clock.J m) (a.clock.hatBeta m) (a.clock.hatBeta (m+1))
variable {a: Levels G}
lemma bigger (m:ℕ)(E:Ember a m)(p:ℕ): Bid.Larger (G:=G) (a.clock.op m p):=by
 let H:=a.S
 have hu:= a.fits.sizeT m p
 refine ⟨(a.blocks m p).branches,?_,?_⟩
 · have hh: H.side m p ≤ H.side (m+1) p:= Nat.mul_le_mul_left _ (H.den_strict.monotone (Nat.le_succ m))
   apply le_trans (Nat.mul_le_mul_left 100 E.sized) (le_trans _ hh); exact (Nat.mul_le_mul_left 100 (Nat.le_add_right ..)).trans hu
 change 1 < (a.S.side m p).val; change 100*(_+1) ≤ (a.S.side m p).val at hu; omega

/-- Does not require estimates from this test at startup. -/
def Vigil (a:Levels G): Prop:=∀ᶠ m:ℕ in atTop, Nonempty (Ember a m)
-- two-stage demands (covers all towers of a). proof without factoring θ. Post waits only hatβ.
lemma vroom (s:Sheet G) : ∃ τ:ℕ→ℕ,∀ k:ℕ→ℕ,τ ≤ k→ let T: Sheet G:= {s with floorL:=k}; ∀ M:Rolls T, ∃ B:ℕ→ℝ,∀ (θ: Protection M)(W:Delays θ), B ≤ W.betaEntry → ∀ (A:RG.Supply.Bar W)(I:Wait A)(a:Levels G), Paid I a→ Vigil a := by
 choose! t h using fun j i hj hi=> post_phase (s.profile j) G s.kernel j i hj hi
 let V (i):= (t i i) ⊔ (t i (i-1))
 refine ⟨V,?_⟩; intro k hK T M
 have hy(j:ℕ)(x:4 ≤ j):∃ A:Patch,A.L=M.L j∧A.J=j:=⟨⟨_,_,x,(M.large j).size,(M.large j).odd⟩,rfl,rfl⟩
 haveI : Nonempty Patch:= ⟨(hy 4 le_rfl).choose⟩
 choose! A hA ht using hy
 let K(j):= G.slopeConstant*Real.log ((A j).L.val:ℝ)
 have hp(j:ℕ)(hv: 5 ≤ j)(i:ℕ)(hx:4 ≤ i)(hℓ:i=j∨i=j-1): ∀ᶠ b:ℝ in atTop,Nonempty (Eon G (s.profile j) s.kernel (A j) i b (b+K j)):=by
    have hm : 4≤j:=by omega
    refine h j i hv hx (A j) (ht j hm) ?_ _; rw[hA j hm]; apply le_trans _ ((hK j).trans (M.large j).need); cases hℓ with
    | inl v=>exact v.symm ▸ le_sup_left (a:= t j j) (b:=t j (j-1))
    | inr v => exact v.symm ▸ le_sup_right (a:= t j j) (b:=t j (j-1))
 have he(j:ℕ)(h:5 ≤ j): ∃ v:ℝ,∀ b,v ≤ b→ ∀ i:ℕ,4≤ i → i≤j → j≤ i+1 → Nonempty (Eon G (s.profile j) s.kernel (A j) i b (b+K j)) :=by
    apply eventually_atTop.mp; filter_upwards [hp j h j (by omega) (Or.inl rfl), hp j h (j-1) (by omega) (Or.inr rfl)] with v hv he i hi ht hf
    rcases show i=j ∨ i=j-1 by omega with h|h
    · subst i; exact hv
    subst i; exact he
 choose! B hb using he; refine ⟨B,fun θ W hW C I a ha=>?_⟩
 refine (a.fits.deep.eventually_ge_atTop 5).mono (fun m hm=>?_)
 have hy: 5 ≤ a.clock.J (m+1):= hm.trans (a.fits.mono (Nat.le_succ _)); let j:= a.clock.J (m+1); let i:= a.clock.J m; let P:=(a.clock.op m 0).patch
 have hx : P=A j :=by
    have he: (A j).J=j:=ht j (by omega); have hX:P.L=(A j).L:= by rw[hA j (by omega)]; exact (a.fits.sameFactor _).symm.trans (congr_fun ha.lengths j)
    have pJ : P.J=j:=rfl; have ht:P.J=(A j).J:=pJ.trans he.symm; generalize P=W at hX ht ⊢; generalize A j=V at hX ht ⊢; cases W; cases V; congr
 let E:=a.clock.hatBeta; have he': E (m+1)=E m+K j:=by unfold E K Calendar.hatBeta; rw [Schedule.scale_succ,← hx]; change (_:ℝ) + _ = _+ _*Real.log ((a.S.block m).val:ℝ); ring
 change Nonempty (Eon G (a.params (m+1)) a.clock.kernel P i (E m) (E (m+1))); have hy': a.params (m+1)= s.profile j:= congr_fun ha.stage _; rw [ha.kernel,hx,he',hy']; exact hb j hy (E m) ((hW _).trans (ha.pays m)) i (a.clock.adm _) (a.fits.mono (Nat.le_succ m)) (a.fits.stepSlow _)
end YM.Trace.Perfect
