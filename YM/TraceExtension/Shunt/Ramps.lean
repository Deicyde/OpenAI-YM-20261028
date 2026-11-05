import YM.TraceExtension.Shunt.Post
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shunt
open RG Wilson Lattice Source Labels Finset Push.Local Next.Foundations MergeProof Planned.GuardedAtom Guard Extra.Histories Filter Function Relay
open MeasureTheory
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side} (T:SectionData F)(H:Hol G)(R:Rep G n){v w c k:ℝ}
structure Proxy (Z : Support n)(X:Coefficient F n)(f:Film G n)(t v w:ℝ):Prop where
   format : X.Format 0 H R
   charge : ∃ a, F.coeffSize X.x+a≤ v ∧ X.remBound 0 R (Real.sqrt t) a
   naked : X.forced=0
   pose(U) : Healthy R.p.threshold Z U→ X.exponentialEntry 0 T R U= f U
   all(U): ‖X.exponentialEntry 0 T R U‖ ≤ w
   locale : UsesFinal R.p.threshold Z (X.exponentialEntry 0 T R)
   symm : GaugeInvariant (X.exponentialEntry 0 T R)
   pay : Measurable (X.exponentialEntry 0 T R)
lemma proxD {X : Coefficient F n}{P:Support n}{f:Film G n}(h: Proxy T H R P X f v c k) : AtomD T H R X (X.exponentialEntry 0 T R) v c 0:=by
   refine ⟨h.format,h.charge,⟨0,Attainment.blank _,?_⟩,fun U=> ?_⟩
   · rw[h.naked]; funext i U; unfold profile cram hook; simp
   unfold Coefficient.density Coefficient.marked; simp[h.naked]
def secondary(P:Support n)(Z : Film G n):Coefficient F n:= ⟨weighted H F 0 P R.p.threshold Z,fun _=> P,Pi.single (0:ℕ) (Push.Local.residual H T 0 P R.p.threshold Z),0⟩
lemma ramps (R:Rep G n)(P:Support n)(Z:Film G n)(h:Readable H T R.p n c) (hp: T.footprint (0:Site n)⊆ P)(hR:R.p.Regular P Z)(hz:R.p.supBounds (0:Site n) P Z w)(hv:0 < v):
    let Q:= secondary T H R P Z; let A:= atomPrice H F c*w; let B:=readPrice H F*w
    Proxy T H R P Q Z v (B+ R.p.mass P A) ((1+c)*B+A):=by
    intro Q a b; let f:= Push.Local.residual H T 0 P R.p.threshold Z; let F':= Push.Local.primary T (0:Site n) R.p.threshold Q.x; let x:= masked R.p.threshold P f
    obtain ⟨hh,h₁,hT,H'⟩:=convert_atom 0 h hR; have hG:= charge_atom 0 h hR hz
    have hp':joint T (0:Site n) P=P:=Finset.union_eq_left.mpr hp
    obtain ⟨hx,ht⟩:= (reads_null_iff ..).1 hT
    have hP:R.p.Regular P f:=hp' ▸ hh; have hg:R.p.supBounds 0 P f a:= hp' ▸ hG.1
    have hF : R.p.Regular (T.footprint (0:Site n)) (presented T 0 R.p.threshold (F.core Q.x)):= (presented_good 0 h _).1
    have hF' : F.coeffSize Q.x ≤ b:= weighted_bound H F 0 hR h.order h.power hz
    have hQ(U):Q.exponentialEntry 0 T R U= F' U + x U:=by
        unfold Coefficient.exponentialEntry; apply congr_arg₂ _ rfl; rw[tsum_eq_single 0]; unfold Coefficient.maskedTerm; rw [show Q.regular 0=f from (by simp only[Q,secondary,Pi.single_eq_same]; rfl)]; rfl; intro j hj; unfold Coefficient.maskedTerm; rw [show Q.regular j=0 from Pi.single_eq_of_ne hj ..]; simp[masked]
    refine ⟨⟨fun i=> ?_,fun i=>show _∈P from hp' ▸ h₁,fun i=>?_,fun i hi=> ?_,fun _ _ H=> (H rfl).elim,fun _ H=>(H rfl).elim,fun i g U=>rfl,fun i U V h h'=>rfl,fun _=>measurable_const⟩,⟨_,add_le_add_left hF' (R.p.mass P a),?_⟩, rfl,fun U hh=> ?_,fun U=> ?_, ?_,?_,?_⟩
    · by_cases he:i=0
      · subst i; simp only [Q,secondary,Pi.single_eq_same]; exact hP
      simp only [Q,secondary,Pi.single_eq_of_ne he ..]; exact regular_const 0
    · by_cases he:i=0
      · subst i; simp only[Q,secondary,Pi.single_eq_same]; exact hx
      simp only[Q,secondary,Pi.single_eq_of_ne he ..,Pi.zero_apply]
    · by_cases he:i=0
      · subst i; simp only [Q,secondary,Pi.single_eq_same]; exact ht (hp'.symm ▸ (show Nonwrapping P 0 from hi))
      rw [show Q.regular i=0 from by simp [Q,secondary,he]]; exact fun J=> ⟨contDiffAt_const,fun k hk=>by change iteratedDeriv _ (0:ℝ→ℂ) _ =_;simp⟩
    · refine ⟨_,0,(R.p.loMass P a hg.1|>.trans' hg.1),le_rfl,(add_zero _).le, Real.sqrt_pos.mpr hv,⟨Pi.single 0 a,?_,fun i=>?_⟩,⟨0,?_,fun i=> ⟨le_rfl,fun _=>norm_zero.le⟩⟩⟩
      · rw [show (fun i:ℕ=> R.p.mass (Q.support i) ((Pi.single 0 a:ℕ→ℝ) i))=Pi.single 0 (R.p.mass P a) from ?_]; rotate_left
        · funext i; by_cases he:i=0; subst i; simp[Q,secondary]; simp[Pi.single_eq_of_ne he,BudgetPoint.mass]
        exact ⟨fun i=> by by_cases he:i=0; subst i; rw[Pi.single_eq_same]; exact (R.p.loMass P a hg.1|>.trans' hg.1); rw[Pi.single_eq_of_ne he], (hasSum_pi_single _ _).summable,by simp⟩
      · by_cases he:i=0
        · subst i; simpa only [Q,secondary,Pi.single_eq_same] using hg
        rw [show Q.regular i=0 from Pi.single_eq_of_ne he _,Pi.single_eq_of_ne he]; simpa [Q,secondary] using bound_smul 0 hg
      simp [SumBudget,BudgetPoint.mass]
    · rw [hQ,show F' U=presented T _ _ _ U from presented_primary _ h.sound _ U (Disjoint.mono_left hp hh),show x U=f U from masked_eq _ _ _ _ hh]; change _+ (Z U-presented T 0 _ Q.x U)=_; ring
    · rw [hQ]; apply (norm_add_le ..).trans; refine add_le_add ((primary_price 0 h Q.x U).trans (mul_le_mul_of_nonneg_left hF' (by positivity[h.nonneg]))) ?_; unfold x; by_cases ht:Healthy R.p.threshold P U; rw [masked_eq _ _ _ _ ht]; exact hg.2 U ht [] (by simp) (by simp); rw [masked_ne _ _ _ _ ht,norm_zero]; exact hg.1
    · intro U V hh hp''; rw [hQ,hQ]; apply congr_arg₂ (· + ·) _ (uses_mask _ hP.sites _ _ hh hp''); exact congr_arg₂ (· + ·) rfl (Work.H03.reads_larger hp (uses_mask R.p.threshold hF.sites) U V hh hp'')
    · intro g U; rw [hQ,hQ]; exact congr_arg₂ (· + ·) (show F' (gauge g U)=F' U from congr_arg₂ (· + ·) rfl ((invariant_mask hF.symmetry R.p.threshold (T.footprint (0:Site n))) g U)) (show x (gauge g U)=x U from invariant_mask hP.symmetry _ _ g U)
    rw[funext hQ]; exact Measurable.add (Measurable.add measurable_const (masked_measurable _ _ _ hF.borel)) (masked_measurable _ _ _ hP.borel)
end YM.Trace.Shunt
