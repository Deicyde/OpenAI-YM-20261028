import YM.RG08.Needle.Garbs
/-!
# Reconfigure fibers and support at all n. Canonical operation fixed
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Needle
open RG Laurent Lattice Wilson Bloch Exterior Precision Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall Vale Reflect Staffer Loom PertExtension.Series.Radial PertExtension.Series.Tested
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {α I: Type} {G: Gauge} {L c f p: Side}{w R A B:ℝ}{D d e j r n i k t:ℕ}{τ:ℕ}
variable {X:Row (Park G L) (Loc G 1)} {V U: BoardU D R G}{H : Canticle (Park G L)}{M : Row (Fink G L) (Fink G L)}{Q: Cross L (Loc G 1) (Loc G 1)}{W : Repeated L} {Θ : EnvelopeU D R G r}
lemma carpet_costp (p: Site L)(i:Beads α r): mint k (carpet p i) ≤ mint k i := by
  apply Finset.prod_le_prod (fun _ _=> Carrier.liftCost_pos ..); intro j _; change (1+↑(size (carry p (i j).1)))^k≤ (1+ (size (i j).1:ℝ))^k; gcongr; exact carry_size ..
lemma shift_paidP (he:Odd L.val)(hp:1/2≤R)(hV:Polished Θ)(p: Site L): Polished (shiftP p (fun i=> readdress (Θ i) p)) := by
  intro k; obtain ⟨C,hV⟩:= hV k; refine ⟨_, Ink.pour _ (show Quire.Ink _ _ C from budget_mono hV ?_ ?_) (mint_one (Co L (Loc G 1)) r k)⟩
  · exact fun i=> mul_nonneg (mint_pos _ _ _ (carpet p i)) (norm_nonneg _)
  intro i; exact mul_le_mul (carpet_costp p i) (read_scores he hp p (Θ i)).1 (norm_nonneg _) (mint_pos _ _ _ _)
lemma creams_have (he:Odd L.val)(hp:1/2≤R)(hU:Lank U) : Lank (cream d U L) := fun i j=> polished_sum (fun z _=> polished_scale (rung_price skylight_ok (shift_paidP he hp (hU i j) z)) _)
lemma capstan (hp:Whole M)(h:Whole Q)(hu:Fits τ U)(he:Odd L.val)(hf:∀ i j,Tidy (U i j))(hx:∀ i j,Tunable (H i j))(hP:Decked H)(hr:1/2≤R)(hg:∀ i j, Glows (H i j))(hU: Lank U)(d:ℕ): Lank (filop M Q H none τ d U) := by
  intro i j
  apply rung_price (scan_whole h) (polished_sum (fun _ _=>treble_shelf (veiled_whole hp) hx hg ((creamy d L hu (fun i j=>(hf i j).pens) hr he).2) (creams_have he hr hU) i j))

def Same [AddCommGroup α] (U V:ℕ→α) (e:ℕ) := ∀ i≤e,U i=V i
lemma mute_same {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]{U V: Screed E α}{K:Row α α}{A:Canticle α}(h:Same U V e)(hp:i≤e): murmur none K A U n i r= murmur none K A V n i r := by
  induction n using Nat.caseStrongRecOn generalizing i r with
  | zero=> rw [murmur,murmur,h i hp]
  | ind n ih=> rw [murmur_step,murmur_step,ih n le_rfl hp]; congr 2; apply sum_congr rfl; intro b hb; apply sum_congr rfl; intro a ha; rw [funext (show ∀ r, murmur none K A U b.1 a.1 r=murmur none K A V b.1 a.1 r from fun r=> ih b.1 (by have he:=mem_antidiagonal.mp hb; omega) (by have he:=mem_antidiagonal.mp ha; omega))]
lemma filop_init (h:Same U V e)(d:ℕ): Same (filop M Q H none τ d U) (filop M Q H none τ d V) e := by
  intro i hi; funext r; unfold filop; congr 1; apply sum_congr rfl; intro n hn; exact mute_same (show Same (cream d U L) (cream d V L) e from fun i hi=> by funext r; unfold cream reelF; rw [h i hi]) hi
lemma hill_init (h:Same U V e)(t: PowerSeries ℝ): Same (hill t U) (hill t V) e := by
  intro i hi; funext r; apply Finset.sum_congr rfl; intro x hx; rw [h x (by have he:=mem_range.mp hx; omega)]
lemma audit_init (H:Hol G)(F:Labels.Frame G d)(h:Same U V e): Same (auditT H F U) (auditT H F V) e := by
  intro i hi; funext b; apply sum_congr rfl; intro r hr; rw [h (i+r-slot b) (by have he:=mem_range.mp hr; omega)]

-- Rank-high saturation at top valuation
private lemma mute_top (hp:Whole M) {V:Screed (Voice D R) (Park G L)}(hU: Fits τ V)(hf:∀ j e,Tidy (V j e))(hx:∀ i j,Tunable (H i j))(he:Decked H) : murmur none (veiled M) H V (n+1) 0 τ=0 := not_ne_iff.mp (mt (murmur_degree (veiled_whole hp) hx he hf hU) (by omega))
lemma almost (Q:Row (Fink G L) (Loc G 1))(he:Odd L.val)(hX:1/2≤R)(hp:Fits τ U)(hV:∀ j k,Tidy (U j k))(hQ:Whole M)(hg: Decked H)(hx:∀ i j,Tunable (H i j)): halfU d (veiled M) H τ U 0 τ=0 := sum_eq_zero fun p _=> by
  obtain ⟨hv,hB⟩:= creamy d L hp (fun i j=>(hV i j).pens) hX he; exact mute_top hQ hv hB hx hg
-- halo of zero already established; halo linear exact from periods
lemma zero_aboard (t:ℕ)(he:Odd L.val)(hp:1/2≤R)(hx:Whole Q): aboard t Q (0:EnvelopeU D R G r)=0 := by
  unfold aboard; rw [sum_eq_zero,smul_zero]; intro i _; unfold Vale.halo belly revolve sires Shade.readdress; simp only [he,hp,true_and,↓reduceDIte,Pi.zero_apply]; funext g; change (∑' j,_ • (0:Voice _ _))=0; simp
lemma active_add {V:EnvelopeU D R G r}(he:Odd L.val)(hp:1/2≤R)(hx:Whole Q)(i:Site L)(hV:Tidy V)(ht:Tidy Θ): Vale.halo i (V+Θ) Q=Vale.halo i V Q+Vale.halo i Θ Q := by
  apply envelope_ext; intro φ; let E:=plug φ R; apply Tidy.uniquely (Tidy.map _ (halo_tid he hp (hV.plus ht) hx)) (Tidy.map _ ((halo_tid he hp hV hx).plus (halo_tid he hp ht hx))); intro c; funext x
  have hz : ∀ A B: EnvelopeU D R G r,E∘ (A+B)=E∘A+ E∘ B:= fun A B=> funext fun i=>map_add ..
  let v: Ratio c (c*L):= ⟨L,rfl⟩
  rw [hz, root_plus _ ((halo_tid he hp hV hx).pens.shaped _) ((halo_tid he hp ht hx).pens.shaped _),Pi.add_apply]; unfold E at *
  rw [halo_pay v 0 i Q (V+Θ) (hV.plus ht) _ hx he hp,halo_pay v 0 i Q V hV _ hx he hp,halo_pay v 0 i Q Θ ht _ hx he hp]
  let P:=plug (roll (spinner i) (Carrier.unitStep L) φ) R
  change rootSong (P∘(V+Θ)) _ _ _ = _; rw [show P∘(V+Θ)=P ∘ V + P ∘ Θ from funext fun i=>map_add ..,root_plus _ (hV.pens.shaped P) (ht.pens.shaped P)]; rfl
lemma aboard_add {V :EnvelopeU D R G r}(he:Odd L.val)(hp:1/2≤R)(hx:Whole Q)(hV:Tidy V)(ht:Tidy Θ)(m:ℕ): aboard m Q (V+Θ)=aboard m Q V+aboard m Q Θ := by unfold aboard; simp_rw [fun i:Site L=>active_add he hp hx i hV ht,sum_add_distrib,smul_add]
lemma aboard_sub {V :EnvelopeU D R G r}(he:Odd L.val)(hp:1/2≤R)(hx:Whole Q)(hV:Tidy V)(ht:Tidy Θ)(m:ℕ): aboard m Q (V-Θ)=aboard m Q V-aboard m Q Θ := eq_sub_of_add_eq (by rw [← aboard_add he hp hx (hV.less ht) ht, sub_add_cancel])
-- exact structural Tale
end YM.RG08.Needle
