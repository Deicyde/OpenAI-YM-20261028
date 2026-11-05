import YM.UVExtension.Steady.Swift
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Weights

/-! Fixed level rooted prices implication full ledger tight. No compact
Volume assertion status on support. Can be used for physical polys. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Steady
open Filter Function Metric Set RG Lattice Pressure Push.AbsoluteSums Finset ConnectedActivityE6
open scoped BigOperators Topology ContDiff Classical
variable {ι κ π : Type*}{v:Filter ι}
namespace Swift
variable {a b:ι→κ→ℝ} {n:Side} {r s:ℝ} {d B:ℕ}
lemma spared {X:κ→Support n}{w : κ→ℝ}{p b:ℝ}(h:Ac.Hit X B w p b)(hp:0 ≤ p) (hr:∀ i,0 ≤ w i)(hs:∀ i,w i≠0 → (X i).Nonempty): SumBudget w ((Fintype.card (Site n):ℝ)*b):=by
  let f (x:Site n) i:= if x∈X i then w i*Real.exp (p* coverNumber B (X i)) else 0; have hp' := budget_over Finset.univ f _ (fun i _=>h i); rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hp'
  refine budget_mono hp' hr ?_; intro i; by_cases he:w i=0
  · rw [he]; exact hp'.1 _
  obtain ⟨x,hx⟩:= hs i he; have hh : w i≤f x i:= by unfold f; rw [if_pos hx]; exact le_mul_of_one_le_right (hr _) (Real.one_le_exp (by positivity))
  exact hh.trans (Finset.single_le_sum (fun j _=> (h j).1 i) (Finset.mem_univ x))
lemma ranked {w:ι→κ→ℕ}(p:∃ r:ℝ,0 ≤ r ∧ ∀ᶠ n in v, SumBudget (fun i=> (1+(w n i:ℝ))*a n i) r)(h:∀ y:ℕ, Swift v (fun n i=> if w n i≤y then a n i else 0)):
    Swift v a:=by
  obtain ⟨r,hr,hp⟩:=p
  have hf : ∀ᶠ n in v,SumBudget (a n) r:=by
      filter_upwards [hp] with n ht
      have hs i : 0 ≤ a n i := nonneg_of_mul_nonneg_right (ht.1 i) (by positivity : 0 < 1+(w n i:ℝ))
      exact budget_mono ht hs (fun i=> le_mul_of_one_le_left (hs _) (le_add_of_nonneg_right (by positivity)))
  apply absorbs ⟨_,hf⟩; intro ε he; obtain ⟨N,hN⟩:= exists_nat_gt (r/ε); let f n i:= if w n i≤N then a n i else 0; let g n i:= if w n i ≤ N then 0 else a n i
  refine ⟨f,g,h _,?_,Eventually.of_forall (fun n i=> by unfold f g; split <;> simp)⟩; filter_upwards [hp,hf] with k hk hq
  have ht:(r/(1+N)) ≤ ε:=(div_le_iff₀ (by positivity)).mpr (by have h: r<(N:ℝ)*ε:= (div_lt_iff₀ he).mp hN; linarith)
  refine budget_loosen (D:=ε) (C:=r/(1+N)) ?_ ht
  rw [div_eq_inv_mul]; refine budget_mono (budget_scale (by positivity : 0 ≤ ((1:ℝ)+↑N)⁻¹) hk) (fun i=>by unfold g; split; rfl; exact hq.1 _) ?_
  intro i; unfold g; split; next hb=> exact mul_nonneg (by positivity) (hk.1 i)
  next hb =>
    calc
      _ = (((1:ℝ)+↑N)⁻¹) * (((1:ℝ)+↑N)*a k i):= (inv_mul_cancel_left₀ (show (1:ℝ)+↑N≠0 by positivity) _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (add_le_add_right (by exact_mod_cast (not_le.mp hb).le) _) (hq.1 _)) (by positivity)
-- Money on each head before Finset unrestricted. factor size absorbed by exponent test at level, tail/composition
lemma power_all (σ: Finset κ) (a:κ→ℝ): ∏ i∈σ, (1+a i)= ∑ i∈σ.powerset,∏ j∈i,a j:= by calc
   _ = ∏ i∈σ,(a i+1):= prod_congr rfl fun _ _=> add_comm ..
   _ = _ := by simpa using! Finset.prod_add a (fun _=> 1) σ
lemma unlocked (a:κ→ℝ){r:ℝ}(h:SumBudget a r): SumBudget (fun s:Finset κ=>∏ i∈s,a i) (Real.exp r):=by
    have hs (x:Finset κ):0≤∏ i∈x,a i:= Finset.prod_nonneg (fun i _=> h.1 _)
    refine budget_of_sum hs ?_; intro s; let Z:= s.biUnion id
    apply (sum_le_sum_of_subset_of_nonneg (t:=Z.powerset) (fun i hi=> mem_powerset.mpr (subset_biUnion_of_mem id hi)) (fun j _ _=>hs j)).trans; rw [← power_all]
    refine (prod_le_prod (fun i _=> by linarith [h.1 i]) (fun i _=> le_trans (le_of_eq (add_comm _ _)) (Real.add_one_le_exp (a i)))).trans ?_; rw [← Real.exp_sum]; exact Real.exp_monotone (budget_sum h _)
lemma powerList (p:Swift v a): Swift v (fun n (s:Finset κ)=> ∏ i∈s,a n i):=by
    obtain ⟨r,hr,h⟩:=p.tills; constructor
    · exact ⟨_,h.mono fun n hn=> unlocked _ hn⟩
    intro ε he; obtain ⟨s,hs⟩:=p.drops _ (show 0<ε/Real.exp r from by positivity); refine ⟨s.powerset,?_⟩
    filter_upwards [hs,h] with n hv hy
    let f: Finset κ→ ℝ := fun w=>∏ i∈w,a n i
    have hh:= unlocked _ hy
    -- Tail assign one offender. zero-subset.
    let g(w:Finset κ):= if w∈s.powerset then (0:ℝ) else f w
    have he w(hw:g w≠0): ¬w⊆s:= fun h=> hw (if_pos (mem_powerset.mpr h))
    let Z:= {w|g w≠0}
    let e(w:Z):= Finset.not_subset.mp (he w w.prop)|>.choose
    have ht(w:Z): e w∈ w.val ∧ e w∉ s:= Finset.not_subset.mp (he w w.prop)|>.choose_spec
    let A(w:Z): κ×Finset κ:= ⟨e w,w.val.erase (e w)⟩
    have hA(w:Z):g w.val=a n (e w)*f (A w).2:= (if_neg (mt mem_powerset.mp (he w w.prop))).trans (mul_prod_erase _ (a n) (ht w).1).symm
    have hx : Injective A:=by intro i j H; have h' := congr_arg (fun r:κ×Finset κ=> insert r.1 r.2) H; dsimp [A] at h'; exact Subtype.ext ((insert_erase (ht _).1).symm.trans (h'.trans (insert_erase (ht _).1)))
    have hZ : SumBudget (fun i:Z=> g i) ε:= by
      apply budget_loosen (C:= (ε/Real.exp r)*Real.exp r) ?_ (le_of_eq (by field_simp))
      have h' := budget_pull _ hx (budget_prod hv hh)
      convert h' using 1; ext i; rw [hA]; dsimp only [A,f]; rw [if_neg (ht _).2]
    have hy : SumBudget g (Real.exp r):=budget_mono hh (fun i=>by unfold g; split; rfl; exact hh.1 _) (fun i=>by unfold g; split; exact hh.1 _; rfl)
    have hx : ∑' i,g i=∑' i:Z,g i := (tsum_subtype_eq_of_support_subset (f:=g) (s:=Z) (Subset.rfl)).symm
    convert (show SumBudget g ε from ⟨hy.1,hy.2.1,hx.trans_le hZ.2.2⟩) using 1; rename_i v; try (ext a; simp [g,f])
lemma flourish (p:Swift v a)(j:ℕ): Swift v (fun n (s:Finset κ)=> (s.card:ℝ)^j*∏ i∈s, a n i):=by
    let C:ℝ:= j.factorial; have hC:0≤C:=Nat.cast_nonneg _; let z : ℝ := Real.exp 1; have hz:0 ≤ z:= (Real.exp_pos _).le; obtain ⟨r,hr⟩:= p.books; apply (((p.scales z hz).powerList).scales C hC).le
    filter_upwards [hr] with i h s; have hv: 0 ≤ ∏ j∈ s,a i j:= prod_nonneg fun j _=> h.1 _; refine ⟨by positivity,?_⟩
    rw [prod_mul_distrib,prod_const, ← mul_assoc]; apply mul_le_mul_of_nonneg_right _ hv
    unfold C z; rw [← Real.exp_nat_mul, mul_one,mul_comm]; exact (div_le_iff₀ (by positivity)).mp (Real.pow_div_factorial_le_exp _ (by positivity) _)
end Swift
end YM.UVExtension.Steady
