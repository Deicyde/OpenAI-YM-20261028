import YM.AnalyticNext.QUARTIC_MATCH.Cells.Drop

/-!
# Multi-leg exterior lift theorem

In real position variables. Cf. E item 4 (`n≥3` first lifting,  ff).
Costs quantified before path forecasting. Uses degree >4 cut; doesn't prove
that claim for use in other dimensions, or for $n=2$. The OTHER kind of lift
there (ambiguity/null tensors) is not required for this classical matching.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.BoxChain
open Lattice Exterior Function Filter Topology Drop
open scoped Topology BigOperators

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Lift the last leg preserving closure in all others. -/
theorem at_last (n r : ℕ) (hr : 4 < r+2*n) (hP : 0<r) (σ : ℝ) (he : 0<σ) :
    let k := Fin.last n
    ∃ u d : ℝ, 0<u ∧ u≤σ ∧ 0≤d ∧ ∀ (C : ℝ) (A : ArrayC (Fin (n+1)) ℤ V), Pricing A σ C →
      Rank A k r → ClosedSlot A k → (∀ j, j≠k → Rank A j 1 ∧ ClosedSlot A j) →
      ∃ F : ArrayC (Fin (n+1)) ℤ V, Pricing F u (d*C) ∧ Rank F k (r+1) ∧ lower k F=A ∧
        ∀ j, j≠k → Rank F j 1 ∧ ClosedSlot F j := by
  induction n generalizing σ r with
  | zero =>
    intro k
    refine ⟨σ,0,he,le_rfl,le_rfl, fun C A _ hA _ _ => ?_⟩
    have hm (U : Finset Axis) : U.card ≤ 4 := by simpa [Axis] using Finset.card_le_univ U
    have ha : A=0 := funext fun X => hA X (by have ht := hm (X k).2; omega)
    exact ⟨0,by rw [zero_mul]; exact Pricing.zero he, Rank.zero _ _,by rw [ha,map_zero],fun _ _ => ⟨Rank.zero _ _,map_zero _⟩⟩
  | succ n ih =>
    intro i
    let j := Fin.last n; have hi : i=j.succ := rfl
    let y := (0 : Fin (n+1+1))
    have hy : i ≠ y := hi ▸ Fin.succ_ne_zero _
    obtain ⟨a,C,ha,hα,hC,H⟩ := arm (V:=V) i y hy.symm σ he r
    obtain ⟨b,D,hb,hβ,hD,H₂⟩ := arm (V:=V) i y hy.symm a ha (r+1)
    obtain ⟨v,K,hv,hφ,hK,R⟩ := ih (r+2) (by omega) (by omega) (b/2) (by positivity)
    have hl : v≤b := hφ.trans (by linarith)
    obtain ⟨t,M,ht,hτ,hM,E⟩ := arm (V:=V) y i hy v hv 0
    let B := debit a * C
    let L := D * B
    let P := loss b * L
    let J := K * P
    let W := L + debit v * J
    have hh : 0 ≤ J := mul_nonneg hK (mul_nonneg (loss_pos hb).le (mul_nonneg hD (mul_nonneg (debit_pos _) hC)))
    have hz : 0 ≤ W := add_nonneg (mul_nonneg hD (mul_nonneg (debit_pos _) hC)) (mul_nonneg (debit_pos _) hh)
    refine ⟨t,C+debit t*(M*W),ht,hτ.trans (hl.trans (hβ.trans hα)),
      add_nonneg hC (mul_nonneg (debit_pos _) (mul_nonneg hM hz)),?_⟩
    intro U A hp hg hm hu
    obtain ⟨F,hF,hf,Hl,Hg,Hx⟩ := H _ A hp hg hm (fun h => by omega)
    -- First lift may break closure at y. Diagnose by its boundary.
    let G := lower y F
    have H₀ : Pricing G a (B*U) := by unfold B; rw [mul_assoc]; exact hF.smaller y
    have Hz : Rank G i (r+1) := hf.keeps hy
    have hFY : Rank F y 1 := Hg y hy.symm _ (hu y hy.symm).1
    have hY : Rank G y 0 := hFY.descent
    have hpro (k : Fin (n+1)) (hk : k≠j) : k.succ ≠ i := fun hh => hk (Fin.succ_injective _ (hh.trans hi))
    have hV (k : Fin (n+1+1)) (h₁ : k≠y) (h₂ : k≠i) : Rank G k 1 ∧ ClosedSlot G k :=
      ⟨(Hg k h₂ 1 (hu k h₂).1).keeps h₁, (Hx k h₂ h₁ (hu k h₂).2).transverse _⟩
    have hi₀ : ClosedSlot G i := by unfold G; rw [ClosedSlot,lower_switch, Hl]; exact (hu _ hy.symm).2
    obtain ⟨Y,hP',hr',hS',hQ,hW⟩:= H₂ _ G H₀ Hz hi₀ (fun h => by omega)
    -- Y semi-lift. Pivot at degree zero. Its charge is a closed tensor of *higher*
    -- degree on one fewer positions; by induction get primitive of that charge.
    let Q := cut Y
    have hy0 : Rank Y 0 0 := hQ y hy.symm _ hY
    have H₁ : Pricing Y b (L*U) := by unfold L; rw [mul_assoc]; exact hP'
    have hT : Pricing Q (b/2) (P*U) := by unfold P; rw [mul_assoc]; exact cut_both H₁
    have hWQ : Rank Q j (r+2) := rank_cut j hr'
    have hw : ClosedSlot Q j := by unfold Q; rw [ClosedSlot,← cut_lower j H₁,← hi,hS']; exact emptied j hF
    have e (k : Fin (n+1)) (hj : k ≠ j) := hV k.succ (Fin.succ_ne_zero _) (hpro k hj)
    obtain ⟨O,hO,hrO,hKO,hTO⟩ := R _ Q hT hWQ hw (fun k hj => ⟨rank_cut k (hQ k.succ (hpro _ hj) _ (e k hj).1),
      closed_cut k H₁ (hW k.succ (hpro k hj) (Fin.succ_ne_zero _) (e k hj).2)⟩)
    let A' := blank j O
    have hb' : Pricing A' v (J*U) := by unfold J; rw [mul_assoc]; exact priced_blank _ hO
    -- Subtract ∂(delta at pivot carrying that primitive), preserve all remaining closes.
    let Z := Y-lower i A'
    have Hv : Pricing Z v (W*U) := by
      unfold W; rw [add_mul,mul_assoc (debit v)]; exact (H₁.widen hv hl le_rfl).sub (hb'.smaller _)
    have hZO : Rank Z y 0 := hy0.sub ((rank_at j).keeps hy.symm)
    have hzi : Rank Z i (r+2) := hr'.sub ((rank_blank j hrO).descent)
    have hZG : lower i Z = G := by unfold Z; rw [map_sub,lower_twice,sub_zero,hS']
    have hZ k (hk : k≠y) (hj : k≠i) : Rank Z k 1 ∧ ClosedSlot Z k := by
      obtain ⟨m,rfl⟩ : ∃ a : Fin (n+1), k= a.succ := by exact ⟨k.pred hk, (Fin.succ_pred k hk).symm⟩
      have hm : m≠j := fun he => hj (he ▸ hi.symm)
      exact ⟨(hQ _ hj _ (e m hm).1).sub ((rank_blank j (hTO m hm).1).keeps hj),
        (hW _ hj hk (e m hm).2).sub ((closed_blank j m hm.symm (hTO m hm).2).transverse i)⟩
    have ho : EmptySum Z y := by
      apply EmptySum_iff.mpr; unfold Z; rw [cut_sub j H₁ (hb'.smaller i),hi,cut_lower j hb',show A' = blank j O from rfl,cut_blank,hKO]
      exact sub_self _
    have hT0 : ClosedSlot Z y := by
      funext X; rw [lower_at]; apply Finset.sum_eq_zero; intro z _; rw [sect_at]; split
      · rfl
      have he (w : Cover) : peek y X Z (w,insert z (X y).2) = 0 := hZO _ (by simp)
      rw [he,he,sub_self,smul_zero]
    obtain ⟨Z',h1,h2,h3,h4,h5⟩ := E _ Z Hv hZO hT0 (fun _ => ho)
    have e' : lower y (F-lower i Z')=0 := by rw [map_sub,lower_switch, h3,hZG]; exact sub_self _
    refine ⟨F-lower i Z', by rw [add_mul, mul_assoc, mul_assoc]; exact
        (hF.widen ht (hτ.trans (hl.trans hβ)) le_rfl).sub (h1.smaller i),
      hf.sub (h4 i hy (r+2) hzi |>.descent),by rw [map_sub,lower_twice,sub_zero,Hl], fun k hk => ?_⟩
    by_cases he : k=y
    · subst k; exact ⟨hFY.sub (h2.keeps hy.symm),e'⟩
    exact ⟨(Hg _ hk _ (hu k hk).1).sub ((h4 k he _ (hZ k he hk).1).keeps hk),
      (Hx k hk he (hu k hk).2).sub ((h5 k he hk (hZ k he hk).2).transverse i)⟩

section stage
variable {R : Type*} [AddCommGroup R] [One R] {n : ℕ}

def solve (s : List (Fin n)) (A : ArrayC (Fin n) R V) : ArrayC (Fin n) R V :=
    s.foldl (fun B i => lower i B) A
omit [CompleteSpace V] in
lemma solve_empty (A : ArrayC (Fin n) R V) : solve [] A=A := rfl
omit [CompleteSpace V] in
lemma solve_lower (s : List (Fin n)) (j : Fin n) (A : ArrayC (Fin n) R V) :
    solve s (lower j A)=lower j (solve s A) := by
  induction s generalizing A with
  | nil => rfl
  | cons k l ih =>
    change solve l (lower k (lower j A)) = lower j (solve l (lower k A))
    rw [lower_switch, ih]
omit [CompleteSpace V] in
lemma solve_head (s : List (Fin n)) (j : Fin n) (A : ArrayC (Fin n) R V) :
    solve (j::s) A=lower j (solve s A) := solve_lower s j A
omit [CompleteSpace V] in
lemma solve_tail (s : List (Fin n)) (j : Fin n) (A : ArrayC (Fin n) R V) :
    solve (s++[j]) A=lower j (solve s A) := by unfold solve; rw [List.foldl_append]; rfl

/-- Lift all nonanchor arguments. -/
theorem independently (σ : ℝ) (h : 0 < σ) (j : Fin n) (s : List (Fin n)) (hs : s.Nodup) (hj : j∉s) :
    ∃ u d : ℝ, 0<u ∧ u≤σ ∧ 0 ≤ d ∧ ∀ (C : ℝ) (A : ArrayC (Fin n) ℤ V), Pricing A σ C →
      (∀ i ∈ s, Rank A i 1 ∧ ClosedSlot A i) →
      ∃ F : ArrayC (Fin n) ℤ V, Pricing F u (d*C) ∧ A=solve s F ∧
        (∀ i∈s, Rank F i 2) ∧ ∀ i, i∉s → ∀ k, Rank A i k → Rank F i k := by
  induction s generalizing σ with
  | nil => exact ⟨σ,1,h,le_rfl,zero_le_one,fun C A h _ => ⟨A,by simpa using h, rfl,fun _ hk => by simp at hk, fun _ _ _ hh => hh⟩⟩
  | cons a s ih =>
    rw [List.nodup_cons] at hs; rw [List.mem_cons,not_or] at hj
    obtain ⟨u,d,hu,he,hd,H⟩ := arm (V:=V) a j hj.1 σ h 1
    obtain ⟨v,e,hv,hW,hE,H₂⟩:= ih u hu hs.2 hj.2
    refine ⟨v,e*d,hv,hW.trans he,mul_nonneg hE hd, fun C A h hr => ?_⟩
    have hx := hr a (by simp)
    obtain ⟨F,hF,hm,hK,h₁,h₂⟩:= H _ A h hx.1 hx.2 (fun h => by omega)
    have ht i (hv : i∈s) := hr i (List.mem_cons_of_mem _ hv)
    have hl (i : Fin n) (hv : i∈s) : i≠a := fun he => hs.1 (he ▸ hv)
    obtain ⟨B,hB,hG,hw,hy⟩ := H₂ _ F hF (fun i hi => ⟨h₁ i (hl i hi) _ (ht i hi).1, h₂ i (hl i hi)
      (fun h => hj.2 (h ▸ hi)) (ht i hi).2⟩)
    refine ⟨B, by rwa [mul_assoc], by rw [solve_head,← hG,hK],fun i hi => ?_,?_⟩
    · rcases List.mem_cons.mp hi with rfl|hh
      · exact hy i hs.1 _ hm
      exact hw i hh
    intro i hi k hA; rw [List.mem_cons,not_or] at hi
    exact hy i hi.2 k (h₁ i hi.1 k hA)
end stage

/-- Multileg lift. No harmonic exception here. -/
theorem multi (n : ℕ) (hn : 2≤n) (σ : ℝ) (hp : 0<σ) :
    ∃ θ K : ℝ, 0 < θ ∧ θ ≤ σ ∧ 0 ≤ K ∧ ∀ (C : ℝ) (T : ArrayC (Fin (n+1)) ℤ V),
      Pricing T σ C → (∀ i, Rank T i 1 ∧ ClosedSlot T i) →
      ∃ U : ArrayC (Fin (n+1)) ℤ V, Pricing U θ (K*C) ∧
        T=solve (List.finRange (n+1)) U ∧ ∀ i, Rank U i 2 := by
  let j := Fin.last n
  let S := (List.finRange n).map Fin.castSucc
  have he : (List.finRange (n+1))=S++[j] := List.finRange_succ_last
  have hz : (S++[j]).Nodup := he ▸ List.nodup_finRange (n+1)
  have hS := List.Nodup.sublist (List.sublist_append_left S [j]) hz
  have hj : j∉S := by simp only [S,List.mem_map]; rintro ⟨a,-,ha⟩; exact (Fin.castSucc_ne_last a) ha
  obtain ⟨a,u,ha,hσ,hC,H⟩:= at_last (V:=V) n 1 (by omega) (by omega) σ hp
  obtain ⟨b,v,hb,hθ,hD,H₂⟩ := independently (V:=V) a ha j S hS hj
  refine ⟨b,v*u,hb,hθ.trans hσ,mul_nonneg hD hC,fun C T Hc Ht => ?_⟩
  obtain ⟨F,hF,hy,hK,hg⟩ := H _ T Hc (Ht j).1 (Ht j).2 (fun i _ => Ht i)
  obtain ⟨U,hU,hP,hm,hr⟩ := H₂ _ F hF (fun i hi => hg i (fun h => hj ((show i=j from h) ▸ hi)))
  refine ⟨U,by rwa [mul_assoc],by rw [he,solve_tail,← hP]; exact hK.symm,fun i => ?_⟩
  have hI : i∈S ∨ i=j := by have hi := List.mem_finRange i; rwa [he,List.mem_append,List.mem_singleton] at hi
  rcases hI with H|H
  · exact hm i H
  rw [H]; exact hr j hj 2 hy
end YM.AnalyticNext.QuarticMatch.BoxChain
