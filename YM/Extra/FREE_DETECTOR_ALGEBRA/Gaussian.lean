import YM.Extra.FREE_DETECTOR_ALGEBRA.PowerGram

set_option warningAsError false

/-!
# Wick recurrence as induction principle, covariance
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Pair
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder

variable {G : Gauge} {n : ℕ}

abbrev MomentMap (G : Gauge) (n : ℕ) := MultilinearMap ℂ (fun _ : Fin n => WickPol G) ℂ

def removal (x : Points n) (T : MomentMap G n) : Prop :=
    ∀ i : Fin n, ∀ u : Slot G, ∀ W,
      T (update W i (W i * MvPolynomial.X u)) = ∑ k : Pair.Others i, T (update W k.val (extractVar u (x i) (x k) (W k)))

lemma recurs {x : Points n} (hx : x ∈ conf n) : removal x (moment G x) := fun i u W => remove x hx i u W

lemma byAnnihilators {x : Points n} (hx : x ∈ conf n) (T : MomentMap G n) (he : T (fun _ => 1)=1) (hr : removal x T) :
    T = moment G x := by
  let K := moment G x
  let onlist (I : Finset (Fin n)) (W : Fin n → WickPol G) := ∀ i ∉ I, W i=1
  have he (I : Finset (Fin n)) (W : Fin n → WickPol G) (h : onlist I W) : T W=K W := by
    induction I using Finset.induction_on generalizing W with
    | empty => rw [show W=(fun _ => 1) from funext fun a => h a (by simp), he]; exact (constants _).symm
    | insert i I hi ih =>
      have hc (p : WickPol G) : ∀ (W : Fin n → WickPol G), onlist (insert i I) W →
          T (update W i p) = K (update W i p) := by
        induction p using MvPolynomial.induction_on with
        | C c =>
          intro W h
          rw [show (MvPolynomial.C c : WickPol G) = c • 1 by rw [← MvPolynomial.C_mul',mul_one],T.map_update_smul,K.map_update_smul]
          rw [ih _ (fun a ha => by by_cases hi : a=i; simp [hi]; simp [update_of_ne hi, h a (by simp [ha,hi])])]
        | add p q hp hq =>
          intro W h; rw [T.map_update_add,K.map_update_add,hp W h, hq W h]
        | mul_X p i' hp =>
          intro W h
          have eh : removal x K := recurs hx
          set V := update W i p
          rw [show update W i (p * MvPolynomial.X i') = update V i (V i * MvPolynomial.X i') by simp [V], hr i i' V, eh i i' V]
          apply Finset.sum_congr rfl; intro k _
          let q := Pair.extractVar i' (x i) (x k) (W k)
          have he : V k = W k := update_of_ne k.property _ _
          rw [he]; change T (update V k q)=K (update V k q)
          by_cases hv : k.val ∈ I
          · have he : onlist (insert i I) (update W k.val q) := by
              intro a ha
              have he : a ≠ k.val := fun hh => ha (hh ▸ Finset.mem_insert_of_mem hv)
              rw [update_of_ne he,h a ha]
            change T (update (update W i p) k.val q)=K (update (update W i p) k.val q)
            rw [← update_comm k.property]; exact hp _ he
          have hh : q = 0 := by
            unfold q; rw [h _ (by simp [k.property,hv])]; simp
          have hh : update V k q k.val = 0 := by simpa using hh
          exact (T.map_coord_zero _ hh).trans (K.map_coord_zero _ hh).symm
      simpa only [update_eq_self] using hc (W i) W h
  exact MultilinearMap.ext fun v => he Finset.univ _ (fun i hi => (hi (Finset.mem_univ _)).elim)

lemma descend_rotate (s : Ortho) (a : Slot G) {p q : E4} (he : p ≠ q) (P : WickPol G) :
    descend (solO s (rCoeff a)) (mov s p) (mov s q) (pullSol s P) = pullSol s (Pair.extractVar a p q P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.derivation_C,pullSol]
  | add p q hp hq => simp only [_root_.map_add,hp,hq]
  | mul_X P j hp =>
    have hg := leg_cov s (rCoeff a) (rCoeff j) (show p-q∈away from sub_ne_zero.mpr he)
    have hv : descend (solO s (rCoeff a)) (mov s p) (mov s q) (pullSol s (MvPolynomial.X j)) = pullSol s (Pair.extractVar a p q (MvPolynomial.X j)) := by
      have hc : mov s p≠mov s q := (Ortho.motion s).injective.ne he
      nth_rw 1 [← digit_coeff j,pull_digit,descend_digit _ _ hc,← _root_.map_sub,hg]
      simp [entry,pullSol,rCoeff,Pair.extractVar]
    simp only [Derivation.leibniz,smul_eq_mul,_root_.map_add,_root_.map_mul,hp,hv]

lemma updates {α β : Type*} {n : ℕ} [DecidableEq (Fin n)] (f : Fin n→α → β) (W : Fin n → α) (p : Fin n) (y : α) :
    (fun i => f i (update W p y i)) = update (fun i => f i (W i)) p (f p y) := by
  funext i; by_cases he : i=p <;> simp [he]

theorem wick_rotate (s : Ortho) {x : Points n} (hx : x∈conf n) (W : Fin n → WickPol G) :
    moment G (Points.move s x) (fun i => pullSol s (W i)) = moment G x W := by
  let y := Points.move s x
  let T := (moment G y).compLinearMap (fun _ : Fin n => (pullSol s).toLinearMap)
  have h : T = moment G x := by
    apply byAnnihilators hx
    · change moment G y (fun _ => pullSol s (1:WickPol G))=_
      simp only [_root_.map_one]; exact constants _
    intro i u W
    let v := fun i => pullSol s (W i)
    change moment G y _ = ∑ a : Pair.Others i, moment G y (fun j => pullSol s (update W a _ j))
    rw [show (fun j : Fin n => (pullSol s).toLinearMap (update W i (W i * MvPolynomial.X u) j)) = _ from
      updates (fun _ => pullSol (G:=G) s) W i (W i * MvPolynomial.X u)]
    nth_rw 1 [_root_.map_mul, ← digit_coeff u,pull_digit]
    change replace y v i (v i * digit _) = _
    have hy : y∈conf n := fun _ _ h => (show Injective x.ofLp from hx) ((Ortho.motion s).injective h)
    rw [descend_relation _ y i hy]
    apply Finset.sum_congr rfl; intro k _
    rw [updates (fun _ => pullSol s),replace_at]
    rw [show descend (solO s (rCoeff u)) (y i) (y k) (v k) = _ from descend_rotate s u ((show Injective x.ofLp from hx).ne k.property.symm) (W k)]
  exact DFunLike.congr_fun h W

lemma extract_bar (a : Slot G) (p q : E4) (W : WickPol G) : extractVar a p q (barPol W) = barPol (extractVar a p q W) := by
  induction W using MvPolynomial.induction_on with
  | C c => simp [barPol,MvPolynomial.derivation_C]
  | add p q hp hq => simp only [_root_.map_add,hp,hq]
  | mul_X W i he =>
    have hb : extractVar a p q (barPol (MvPolynomial.X i)) = barPol (extractVar a p q (MvPolynomial.X i)) := by simp [barPol,extractVar,entry]
    simp only [_root_.map_mul,Derivation.leibniz,smul_eq_mul,_root_.map_add,hb,he]

theorem wick_bar {x : Points n} (hx : x∈conf n) (W : Fin n → WickPol G) :
    moment G x (fun i => barPol (W i)) = star (moment G x W) := by
  let T : MomentMap G n :=
    { toFun p := star (moment G x (fun i => barPol (p i)))
      map_update_add' p i u v := by
        have he (v : WickPol G) : (fun a => barPol (update p i v a)) = _ := updates (fun _ => barPol) p i v
        simp_rw [he,_root_.map_add, MultilinearMap.map_update_add,star_add]
      map_update_smul' p i t v := by
        have he (v : WickPol G) : (fun a => barPol (update p i v a)) = _ := updates (fun _ => barPol) p i v
        simp_rw [he,bar_scaled, MultilinearMap.map_update_smul, smul_eq_mul,star_mul,star_star]
        ring }
  have h : T=moment G x := by
    apply byAnnihilators hx
    · change star (moment G x (fun _ => barPol (1:WickPol G)))=1
      rw [show (fun _ : Fin n => barPol (1:WickPol G)) = (fun _ => 1) from funext fun _ => map_one _,constants]; simp
    intro i u W
    let p := fun a => barPol (W a)
    change star (moment G x _)= ∑ a : Pair.Others i, star (moment G x _)
    rw [show (fun j : Fin n => barPol (update W i (W i*MvPolynomial.X u) j)) = _ from updates (fun _ => barPol) W i (W i * MvPolynomial.X u),
      _root_.map_mul,show barPol (MvPolynomial.X u) = MvPolynomial.X u by simp [barPol]]
    change star (replace x p i (p i * MvPolynomial.X u)) = _
    rw [remove x hx,star_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [show (fun j : Fin n => barPol (update W k.val (extractVar u (x i) (x k) (W k)) j)) = _ from updates (fun _ => barPol) W k.val _]
    unfold p
    rw [extract_bar]; rfl
  exact (star_star _).symm.trans (congr_arg star (DFunLike.congr_fun h W))
end YM.Extra.FD
