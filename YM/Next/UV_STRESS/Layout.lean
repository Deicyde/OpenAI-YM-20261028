import YM.Next.UV_STRESS.Atom

/-!
# From single-atom replication on Maker to estimates including mixed arrays
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory Analysis Extraction Around Wilson Cells Lattice
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {h k N p n : ℕ} {f : Extraction.Order}

section Step
variable {L : Side} (T : Tiling L) {β : ℝ} (H : Seam G L β)

lemma minus {K : Set (Site L)} {Y X : Config G L → ℂ} (h : Interior K Y) (p : Interior K X) : Interior K (Y-X) := by
  rw [sub_eq_add_neg]; exact h.plus (show Interior K (-X) from (show Interior K (fun x => -X x) from by simpa using p.scale (-1)))

include H in
theorem replace_all (a : Fin n → T.Cell) (Q Y : Fin n → Config G L → ℂ) (M δ : ℝ)
    (hx : Injective a) (hp : ∀ i, Interior (T.chamber 0) (Q i)) (hQ : ∀ i, Interior (T.chamber 0) (Y i))
    (h : ∀ i, T.rootTest β (Q i) ≤ M ∧ T.rootTest β (Y i) ≤ M ∧ T.rootTest β (Y i-Q i) ≤ δ) :
    ‖moment β (fun w => ∏ i : Fin n,T.copy (a i) (Y i) w) - moment β (fun w => ∏ i : Fin n,T.copy (a i) (Q i) w)‖ ≤
      (n:ℝ)*(δ*M^(n-1)) := by
  classical
  let U (s : Finset (Fin n)) (i : Fin n) := if i∈s then Y i else Q i
  let F (s : Finset (Fin n)) w := ∏ i : Fin n,T.copy (a i) (U s i) w
  have he (s i) : Interior (T.chamber 0) (U s i) := by unfold U; split; exacts [hQ i,hp i]
  have hf s : Integrable (F s) (law G _ β) := by
    have ht (i : Fin n) : Interior Set.univ (T.copy (a i) (U s i)) := (T.copies _ (he s i)).enlarges (subset_univ _)
    exact Interior.integrable (Interior.combines _ Finset.univ (fun i _ => ht i)) _
  have hg (s : Finset (Fin n)) : ‖moment β (F s) - moment β (F ∅)‖ ≤ (s.card:ℝ)*(δ*M^(n-1)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj IH =>
      let L := fun i : Fin n => if i=j then Y j-Q j else U s i
      have hL (w : Config G _) : F (insert j s) w-F s w=∏ i, T.copy (a i) (L i) w := by
        have hv : (∏ i ∈ Finset.univ.erase j, T.copy (a i) (U (insert j s) i) w)=
            ∏ i ∈ Finset.univ.erase j, T.copy (a i) (U s i) w := by
          apply Finset.prod_congr rfl; intro i hi; simp [U,Finset.mem_erase.mp hi|>.1]
        unfold F; simp_rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),hv,← sub_mul]
        simp only [L, U, if_pos, Finset.mem_insert_self,hj, ↓reduceIte]
        have hh : T.copy (a j) (Y j - Q j) w=T.copy (a j) (Y j) w-T.copy (a j) (Q j) w := by
          simp only [Tiling.copy,Pi.sub_apply]; split <;> simp [star_sub]
        rw [hh]; congr 1
        apply Finset.prod_congr rfl; intro i hi; rw [if_neg ((Finset.mem_erase.mp hi).1)]
      have hh : ‖moment β (F (insert j s))-moment β (F s)‖ ≤ δ*M^(n-1) := by
        unfold moment
        rw [← integral_sub (hf _) (hf _)]; simp_rw [hL]
        have he i : Interior (T.chamber 0) (L i) := by unfold L; split; exacts [minus (hQ _) (hp _),he s i]
        apply le_trans (T.planted H _ hx L he)
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
        have hy : T.rootTest β (L j) ≤ δ := by simpa only [L,if_true] using (h j).2.2
        refine mul_le_mul hy ?_ (Finset.prod_nonneg (fun i _ => T.root_nonneg β _)) ((T.root_nonneg β _).trans hy)
        calc
          _ ≤ ∏ _ ∈ (Finset.univ.erase j),M := Finset.prod_le_prod (fun i _ => T.root_nonneg _ _) (fun i hi => by
            dsimp only [L]; rw [if_neg ((Finset.mem_erase.mp hi).1)]; dsimp only [U]; split; exacts [(h i).2.1,(h i).1])
          _ = _ := by simp
      calc
        _ ≤ _ := norm_sub_le_norm_sub_add_norm_sub (moment β (F (insert j s))) (moment β (F s)) (moment β (F ∅))
        _ ≤ _ := le_trans (add_le_add hh IH) (by rw [Finset.card_insert_of_notMem hj]; push_cast; linarith)
  simpa [F,U] using hg Finset.univ
end Step
section sum
variable {sideR : Side} (A : Tiling sideR) (β : ℝ)
lemma root_smul (t : ℂ) (f : Config G sideR→ℂ) : A.rootTest β (t • f) = ‖t‖*A.rootTest β f := by
  classical
  have hp := A.cells_positive
  rw [← pow_left_inj₀ (A.root_nonneg β _) (mul_nonneg (norm_nonneg _) (A.root_nonneg ..)) hp.ne']
  let g (i) : ℂ := if A.hand i then star t else t
  have he (i x) : A.copy i (t • f) x=g i * A.copy i f x := by unfold g; by_cases h : A.hand i <;> simp [Tiling.copy,h]
  rw [A.powering,mul_pow,A.powering]; unfold Tiling.rootPower
  have hh : Tiling.fullAt A (fun _ => t • f)=fun x => (∏ i,g i)*Tiling.fullAt A (fun _ => f) x := by
    funext x; unfold Tiling.fullAt; simp_rw [he,Finset.prod_mul_distrib]
  rw [hh]
  have hz (i : A.Cell) : ‖g i‖=‖t‖ := by unfold g; split_ifs with h <;> simp
  simp [moment, integral_const_mul,norm_prod,hz]

lemma root_sum {ι : Type*} (I : Finset ι) (f : ι → Config G sideR → ℂ) (b : ι→ℂ)
    (hp : ∀ i∈I, Interior (A.chamber 0) (f i)) (H : Seam G sideR β) :
    Interior (A.chamber 0) (∑ i∈I, b i • f i) ∧ A.rootTest β (∑ i∈I, b i • f i) ≤
      ∑ i∈I, ‖b i‖*A.rootTest β (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]; refine ⟨Interior.constant _ _,?_⟩
    rw [show (0:Config G sideR→ℂ)=(0:ℂ) • fzero from (zero_smul _ _).symm,root_smul, norm_zero,zero_mul]
  | @insert i I he ih =>
    obtain ⟨hF,h⟩ := ih (fun i hi => hp i (Finset.mem_insert_of_mem hi))
    have hx : Interior (A.chamber 0) (b i • f i) := (hp i (Finset.mem_insert_self ..)).scale _
    simp only [Finset.sum_insert he]; refine ⟨hx.plus hF,?_⟩
    exact (H.semi A _ _ hx hF).trans (add_le_add (le_of_eq (root_smul ..)) h)
where fzero : Config G sideR→ℂ := 0
end sum

abbrev Stones (C : Family G) (d : ℕ) := (C.book.coord d).Index

def piece (C : Family G) (d : ℕ) (i : Stones C d) : C.book.Ref d := Pi.single i 1

lemma pieces_at (d : ℕ) (v : C.book.Ref d) : ∑ j : Stones C d,v j • piece C d j = v := by
  ext1 i
  simp [piece,Finset.sum_apply,Pi.single_apply]

lemma seen_sum {ι : Type*} [Fintype ι] (d : ℕ) (x : Site (C.side N p)) (w : ι→ C.book.Ref d) (b : ι→ℂ) :
    C.seen ⟨d,∑ i,b i • w i⟩ x=∑ i,b i • C.seen ⟨d,w i⟩ x := by
  let L := IsLinearMap.mk' (fun v => C.O N p (d:=d) v x) (C.linearO N p d x)
  change L _=∑ i,b i • L (w i)
  simp
namespace Maker
variable {d : ℕ} (P : Maker C f h d)

def sunset (v : Fin n → Entitled C d) (k N p) (x : Fin n → Cover) (w : Config G (C.side N p)) :=
  ∏ i,P.fine k N p (v i) (wrap _ (x i)) w

/-- Control true on all grid layouts. Only the last estimate requires the
actual cells distinct on this torus. Does not take absolute INSIDE the law. -/
theorem precise (v : Fin n→ Entitled C d) (H : C.Makes) (hp : CellHyp C f) :
    ∃ A : ℝ,0≤A ∧ ∀ k,∃ B : ℝ,0≤B ∧ ∀ᶠ i : ℕ×ℕ in f.fuse, ∀ x : Fin n → Cover,
      let s := P.sunset v k i.1 i.2 x
      Interior Set.univ (paint s) ∧ (∀ w, |s w| ≤ B) ∧
        (Injective ((wrap (C.side h i.2)) ∘ x) →
          ‖moment (C.beta i.1 i.2) (paint s) - C.numeric i.1 i.2 (fun j => (v j).val) (fun j => location C.S h i.1 i.2 (x j))‖ ≤ costHint k * A) := by
  choose A hA B hB hv using fun j => P.nearby H hp (v j)
  let M := 1+∑ j,A j
  have hM : 0 ≤ M := add_nonneg zero_le_one (Finset.sum_nonneg fun i _ => hA _)
  have hh j : A j ≤ ∑ j,A j := Finset.single_le_sum (f:=A) (fun i _ => hA _) (Finset.mem_univ j)
  refine ⟨(n:ℝ)* M^(n-1),mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hM _),fun k =>
    ⟨∏ j, B j k, Finset.prod_nonneg (fun i _ => hB i k),?_⟩⟩
  filter_upwards [eventually_all.mpr (fun j => hv j k),large_mesh f h] with i hi h' z
  obtain ⟨N,p⟩ := i
  let T := center C.S p h' 0; let U := P.sunset v k N p z
  let a : Fin n → T.Cell := wrap (C.side h p) ∘ z
  choose X Y hX hY he hg hu hy hz using fun j => (hi j).choose_spec (a j)
  have hq (w) : U w=∏ j,P.fine k N p (v j) (a j) w := rfl
  have hF : paint U = fun w => ∏ j,T.copy (a j) (Y j) w := by
    funext w
    rw [paint,hq, Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun j _ => congr_fun (hg j) _
  have hw j : C.seen (v j).val (location C.S h N p (z j))=T.copy (a j) (X j) := by
    rw [location,dif_pos h']
    change C.seen (v j).val ((C.S.toDepth h' p).embed (a j))= _
    rw [show (C.S.toDepth h' p).embed (a j)=T.copyMap (a j) 0 from ((copy_home C.S h' 0 (a j)).trans (zero_add _)).symm]; exact he j
  refine ⟨show Interior _ (paint U) from ?_,fun w => ?_,fun hi => ?_⟩
  · rw [hF]; exact Interior.combines (fun i => T.copy (a i) (Y i)) _ (fun i _ => (T.copies _ (hY i)).enlarges (subset_univ _))
  · change |U w| ≤ _; rw [hq,Finset.abs_prod]; exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hz i _)
  change ‖moment (C.beta N p) (paint U) - _‖ ≤ _
  rw [hF,C.num]; simp_rw [hw]; apply le_trans (replace_all T (hp.all N p) a X Y M (costHint k) hi hX hY ?_)
  · exact le_of_eq (by ring)
  intro j
  refine ⟨(hu j).trans ((hh j).trans (le_add_of_nonneg_left zero_le_one)), ?_, hy j⟩
  have ht : costHint k ≤ 1 := inv_le_one_of_one_le₀ (show 1≤sizeHint k by unfold sizeHint; simp)
  have he := (hp.all N p).semi T _ _ (minus (hY j) (hX j)) (hX j)
  exact (sub_add_cancel (Y j) (X j) ▸ he.trans (add_le_add ((hy j).trans ht) ((hu j).trans (hh j))))
end Maker
end YM.Next.UVStress
