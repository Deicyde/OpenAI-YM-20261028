import YM.TraceExtension.Verse.Scene

/-!
# Character moment limit via long lifts

Apply `Ground.arcs` monomial by monomial at fixed length, after identifying ordinary
conjugation of each compressed whole-word factor with its operator adjoint. Expand
ordered products without commuting the operators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Verse
open Set Filter Function OS OS.Ground Org Spec Table Word Analysis Extraction Bid
open scoped Topology InnerProductSpace BigOperators

variable {G : Gauge} {C : Family G} {F : Filter (ℕ×ℕ)} {S : Table C.book} {V : Chamber S timeAxis}
    {A : Spread V} {L : Register G} {b k : ℕ}

lemma distinct_conjugate {w : L.Word} (h : distinct w) : distinct (Word.conjugate w) :=
  locations.mpr (by simpa only [Word.conjugate, List.map_map, Function.comp_def] using locations.mp h)

lemma conj_M {p₀ : A.Resolution} (ht:p₀.Out) (hv:Steady V){x : p₀.X→Table C.book} (hq:∀ i,(x i).Hierarchy)(hp:∀ i,p₀.receives (x i) i) (w : C.book.Word) (h : distinct w) :
    M A (Word.conjugate w) (distinct_conjugate h) = star (M A w h) := by
  let Z := M A (Word.conjugate w) (distinct_conjugate h) - star (M A w h)
  suffices Z=0 by exact sub_eq_zero.mp this
  have he i : p₀.character i Z=0:=by
      unfold Z; rw [map_sub,map_star,Retain.pops _ _ (hp i),Retain.pops _ _ (hp i)]; apply sub_eq_zero.mpr
      have hh : Word.conjugate w = realize (C.book.conjugate ∘ tokens w) (positions w):=by
         conv_lhs=>rw [← rebuilt w]
         simp only [Word.conjugate,realize,List.map_ofFn,comp_def]
      rw [hh,Table.readAt]; exact (hq i).spin.real h (tokens w)
  apply attains A ht.abelian hv Z
  have hh:= ht.ground (star Z * Z)
  simp_rw [map_mul,map_star,he, mul_zero, MeasureTheory.integral_zero] at hh
  have hx := ContinuousLinearMap.adjoint_inner_right Z.val V.omega0 (Z.val V.omega0)
  exact inner_self_eq_zero.mp (hx.symm.trans hh.symm)

private def alt {B : Type*} [Star B] (j : ℕ) (x : B) := if j%2=0 then star x else x

private def carWord (j : ℕ) (r : Row.Core L) : Row.Core L :=
  ⟨if j%2=0 then Word.conjugate r.val else r.val, by split; exact distinct_conjugate r.property; exact r.property⟩

private lemma alt_M {p₀ : A.Resolution} (ht:p₀.Out) (hv:Steady V){x : p₀.X→Table C.book} (hq:∀ i,(x i).Hierarchy)(hp:∀ i,p₀.receives (x i) i) (r : Row.Core C.book) (j : ℕ) :
    M A (carWord j r).val (carWord j r).property = alt j (M A r.val r.property) := by
  unfold alt carWord; split
  · exact conj_M ht hv (x:=x) hq hp ..
  · rfl

private lemma alt_prod {B : Type*} [Monoid B] [Star B] (x : B) (m : ℕ) :
    (List.ofFn fun j : Fin (2*m) => alt j.val x).prod = (star x * x)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ,List.ofFn_succ,List.ofFn_succ,List.prod_cons,List.prod_cons,pow_succ',← ih,mul_assoc]
    simp [alt, Nat.add_assoc]

private def entry (E : Scene C F k) (i : Fin E.num) : Row.Core C.book :=
  ⟨E.word i,(realized _ _).2 (generic_conf _ (E.gen i))⟩

private lemma rises (p : b ≤ k) (i j : ℕ) (hij : i < j) :
    flight (fun t => C.S.gridPoint k (Scene.step C p t i)) (fun t => C.S.gridPoint k (Scene.step C p t j)) := by
  have hp := mul_pos (mul_pos (C.S.a_pos k) (by exact_mod_cast (C.S.toDepth p 0).count.property : 0 < ((C.S.toDepth p 0).count.val : ℝ)))
      (show 0 < 2 * ((j:ℝ)-i) from mul_pos (by norm_num) (sub_pos.mpr (by exact_mod_cast hij)))
  refine (Tendsto.atTop_mul_const hp tendsto_natCast_atTop_atTop).congr ?_
  intro t; simp [Schedule.gridPoint,Scene.step]; ring

private lemma monomial {p₀ : A.Resolution} (ht:p₀.Out) (hv:Steady V){x : p₀.X→Table C.book} (hq:∀ i,(x i).Hierarchy)(hp:∀ i,p₀.receives (x i) i) (hs : S.Hierarchy)
    (p : b ≤ k) (E : Scene C F k) (n : ℕ) (i : Fin (2*n) → Fin E.num) :
    Tendsto (fun t => S.expect (E.flick p t n i)) atTop (𝓝 (inner ℂ V.omega0
      ((List.ofFn fun j : Fin (2*n) => alt j.val (M A (entry E (i j)).val (entry E (i j)).property)).prod.val V.omega0))) := by
  let f (j : Fin (2*n)) : Car C.book := (carWord j.val (entry E (i j)), fun t => C.S.gridPoint k (Scene.step C p t j.val))
  let q := List.ofFn f
  have h : line q := List.pairwise_ofFn.mpr fun a b hab => rises a.val b.val (p:=p) hab
  have ha t : all q t = E.flick p t n i := by rw [all,List.map_ofFn]; rfl
  have hu : starU A (q.map Prod.fst) = (List.ofFn fun j : Fin (2*n) => alt j.val (M A (entry E (i j)).val (entry E (i j)).property)).prod := by
    simp [starU, q, List.map_ofFn, f, Function.comp_def, alt_M ht hv (x:=x) hq hp]
  simpa only [ha,hu] using (arcs A hv hs q h).2

theorem opening {p : A.Resolution} (ht:p.Out) (hv:Steady V){x : p.X→Table C.book} (hq:∀ i,(x i).Hierarchy)(hp:∀ i,p.receives (x i) i) (Y:S.Hierarchy){p':b≤k}(E:Scene C F k) (n:ℕ) :
    Tendsto (fun t=> E.wanted p' t n S) atTop (𝓝 (inner ℂ V.omega0 (((star (E.cluster A)*E.cluster A)^n:A.algebra).val V.omega0))):=by
  let U (i : Fin E.num) := M A (entry E i).val (entry E i).property
  let T := MultilinearMap.mkPiAlgebraFin ℂ (2*n) ↥A.algebra
  let J (j : Fin (2*n)) (i : Fin E.num) := alt j.val (E.factor i) • alt j.val (U i)
  have hu (j : Fin (2*n)) : alt j.val (E.cluster A) = ∑ i, J j i := by
    change alt _ (∑ i, E.factor i • U i) = _
    dsimp only [J, alt]; split <;> simp_all only [star_sum, star_smul]
  have hx : (star (E.cluster A)*E.cluster A)^n = ∑ i : Fin (2*n) → Fin E.num,
      E.price n i • T (fun j => alt j.val (U (i j))) := by
    rw [← alt_prod]
    change T (fun j => alt j.val (E.cluster A)) = _
    simp_rw [hu]; rw [T.map_sum J]
    apply Finset.sum_congr rfl; intro i hi
    exact T.map_smul_univ _ _
  rw [hx]
  change Tendsto _ _ (𝓝 (inner ℂ V.omega0 (A.algebra.subtype _ V.omega0)))
  rw [map_sum, sum_apply, inner_sum]
  simp_rw [map_smul, smul_apply, inner_smul_right]
  exact tendsto_finsetSum _ fun i _ => (monomial ht hv (x:=x) hq hp Y p' E n i).const_mul _
end YM.Trace.Verse
