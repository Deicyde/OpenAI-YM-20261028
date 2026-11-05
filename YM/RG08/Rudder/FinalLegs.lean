import YM.RG08.Rudder.Lines

/-! Project unwanted curvature-rank degrees before taking picture. Then stable
solver need impose only one equation. `lineLift` operates at arity n+1 >= 3. -/
noncomputable section
namespace YM.RG08.Rudder
open scoped lp Topology BigOperators Classical ENNReal
open Forms Packets Finset Function Lattice Pert.Bulk Exterior
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I:Type}{n r:ℕ}

def truth (I:Type)(n:ℕ)(rank:ℕ) : Raw I n→L[ℝ] Raw I n:= ContinuousLinearMap.pi (fun x=> if ∀ i,(x i).2.1.card=rank then ContinuousLinearMap.proj (R:=ℝ) x else 0)
lemma rank_truth (rank:ℕ)(F:Raw I n):Graded (truth I n rank F) (fun _=>rank):=by
 intro y i x hx
 change (if _ then (ContinuousLinearMap.proj (R:=ℝ) (lyre x y):Raw I n→L[ℝ] ℝ) else 0) F =0
 split_ifs with he
 · exact False.elim (hx (he i))
 rfl
lemma intact (rank:ℕ){F:Raw I n}(h:Graded F (fun _=>rank)):truth I n rank F = F:=by
 funext x
 change (if _ then _ else (_:Raw I n→L[ℝ] ℝ)) F = F x
 split_ifs with he
 · rfl
 push Not at he
 obtain ⟨i,hx⟩:= he
 symm; let v(j:Fin n):=((x j).1,(x j).2.1); let z(j:Fin n):=(x j).2.2
 exact h z i v hx
lemma true_held {σ p:ℝ}(rank:ℕ){F:Raw I n} (h:Held (carpet (Tone I)) σ p F): Held (carpet (Tone I)) σ p (truth I n rank F):=by
 apply h.mono le_rfl le_rfl;intro x
 change |(if _ then _ else (_:Raw I n→L[ℝ] ℝ)) F|≤_
 split_ifs <;> [exact le_refl _;exact abs_zero.le.trans (abs_nonneg _)]
lemma true_cohort {F:Raw I n}(h:Cohort F)(r:ℕ):Cohort (truth I n r F):=by
 intro b x
 change (if _ then _ else (_:Raw I n→L[ℝ] ℝ)) F=(if _ then _ else (_:Raw I n→L[ℝ] ℝ)) F
 change (if ∀ i,(x i).2.1.card=r then _ else (_:Raw I n→L[ℝ] ℝ)) F=(if ∀ i,(x i).2.1.card=r then _ else (_:Raw I n→L[ℝ] ℝ)) F
 split_ifs
 exact h b x
 rfl

def lineLift (I:Type)(n:ℕ)(α:ℝ)(F:Raw I (n+1)):Raw I (n+1) := truth I (n+1) 2 (answer 0 α ((picture I (n+1)).comp (truth I (n+1) 2)) F)

/-- **Linear-cost translation-invariant curvature lift on the cover**. choose output
aperture and operator cost at arbitrary arity before block size choices. Reuse the
*same actual lift* on any inputs priced at that Width and their arbitrary differences;
these are literal coefficients, not merely a representative of the difference chosen
after seeing the two cutoffs. Output weaker Held width, arity-factor and preblock price
explicit through pins/trials. Rank two omitted and treated separately. -/
theorem line_legs (I:Type)[Fintype I](n:ℕ)(hn:2≤n)(σ:ℝ)(hs:0<σ):∃ α Q:ℝ,0<α∧α≤σ∧0≤Q∧
   ∀ (F:Raw I (n+1)) (p:ℝ),0≤p→ Cohort F→Graded F 1→Closing F→Held (carpet (Tone I)) σ p F→
      let U:= lineLift I n α F
      picture I (n+1) U=F ∧ Cohort U ∧ Graded U 2 ∧ Held (carpet (Tone I)) (α/2) (Q*p) U ∧
   ∀ (G:Raw I (n+1))(t:ℝ),0≤t→ Cohort G→Graded G 1→Closing G→Held (carpet (Tone I)) σ t G→
      lineLift I n α (F-G)=U - lineLift I n α G:=by
 obtain ⟨θ,K,he,hk,hφ,H⟩:=Ferry I n hn σ hs
 let α:=θ/2
 let a:=Tone I; let L:=(picture I (n+1)).comp (truth I (n+1) 2)
 let fee:=debit' a (n+1) θ; have hf:0≤fee:= debit'_nn he (by omega)
 have hx:0<α:=by unfold α;linarith
 have hp (F:Raw I (n+1))(p:ℝ)(hP:0≤p)(hc:Cohort F)(hr:Graded F 1)(hC: Closing F)(ht: Held (carpet (Tone I)) σ p F):Possible 0 (I:=a) α L (fee*(K*p)) F:=by
    obtain ⟨U,hU,hr,hw⟩:= H p F (NextTo.unit hs hP hc ht (by omega)) hr hC
    refine ⟨hx,mul_nonneg hf (mul_nonneg hφ hP),U,?_,hU.cohort,hU.held (by omega) (mul_nonneg hφ hP) he⟩
    change picture _ _ (truth _ _ _ U)=F
    rw [intact 2 hr,hw]
 let v:=debit' a (n+1) α;have hv:0≤v:=debit'_nn hx (by omega)
 use α,(v*(2*Fintype.card a))*(fee*K)
 refine ⟨hx,by unfold α;linarith,by positivity,?_⟩
 intro F p hP hc hr hC ht U
 have h:=hp _ _ hP hc hr hC ht
 obtain ⟨hEq,hco,hH⟩:=pays h
 refine ⟨hEq,true_cohort hco _,rank_truth 2 _, (true_held _ hH).mono le_rfl (by unfold v; rw [mul_assoc _ _ p,mul_assoc fee K p]) (fun _=>le_rfl),?_⟩
 intro G q hq hu hw hX hY
 change truth I _ _ (answer 0 α L (F-G))=_
 rw [stable h (hp G q hq hu hw hX hY),map_sub];rfl
end YM.RG08.Rudder
