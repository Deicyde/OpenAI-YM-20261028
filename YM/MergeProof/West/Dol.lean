import YM.MergeProof.West.Erl
import YM.Next.RANK.Distant

set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Wall
open Function Set Lattice Wilson RG Normal Perch Prayer  Atlas Station CellsInt Configuration Glimmer Filter Beamer Maxwell
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {n d p k l : ℕ} (A : Levels G)

private def rooted (a : Degree G) (p : Cover) : Degree G := { a with point:=p }
@[simp] private lemma rebased (a : Degree G) : rooted a a.point=a := rfl
private lemma scaledX (x : Points n) (i j : Fin n) (h : x i≠x j) (β e : ℝ) (he : 0<e) (hB : 6 ≤ β) (L S : Degree G) (hg : G.Simple) (ζ : ℕ→ℕ) (hz:Tendsto ζ atTop atTop)(px:ℕ → Points n)(zφ:Tendsto (fun i=> tested A β (ζ i) (px i)) atTop (𝓝 x)) :
    ∀ᶠ k in atTop, ∀ p d H, Model A d (ζ k) p H → ∀ X Y,
      let f:= choose A β (ζ k) (px k)
      let l := rooted L X
      let s := rooted S Y
      let K:= looked (H.κ (ζ k)) (f i) (f j)
      let r:= mag A β (ζ k); let M:= moved (px k) A β i j (ζ k) X Y
      attends d (wood A (ζ k)) l → attends d (wood A (ζ k)) s → (r⁻¹ • M) ∈ Maxwell.away ∧
        ‖amount r l*amount r s*mourn (gesture l) (gesture s) K - gleam L S (r⁻¹ • M)‖ ≤ bill (-4) (clim A (ζ k)) ∧
          ‖amount r l * amount r s*mourn (gesture l) (gesture s) K‖ ≤ bill e (clim A (ζ k)) := by
  have hb : 0<β := by linarith
  obtain ⟨C,c,hc,hC,hH⟩ := range_boundX A x i j h L S hg hb ζ hz px zφ
  filter_upwards [hz.eventually (summer A _ (L.degree+S.degree) hB hg hc hC), hH,
    (((hat_rate A hg).comp hz).eventually ((bill_lo he).eventually_ge_atTop (C+1))),
    (((mag_rate A hg hb).comp hz).const_mul_atTop hc).eventually_ge_atTop 1] with k hu ht hl hV
  intro p d H hp X Y f l s K r M ha hh
  have hz (L : Degree G) (h : attends d (wood A (ζ k)) L) : L.degree ≤ d-1 ∧ street L.point ≤ wood A (ζ k) := by
    rcases h with ⟨he,ht⟩|⟨he,ht⟩
    · exact ⟨by omega,by rw [he,empty_road]; exact Nat.zero_le _⟩
    exact ⟨he.le,ht⟩
  obtain ⟨he,hx,Ht⟩ := ht X Y (hz _ ha).2 (hz _ hh).2
  have hs : 0<r := mag_pos ..
  let g := r⁻¹ • M; have ht : 1≤‖M‖ := le_trans hV he
  have hq : g∈away := smul_ne_zero (inv_pos.mpr hs).ne' (norm_pos_iff.mp (zero_lt_one.trans_le ht))
  have hv := hp.2 (f i) (f j) l s (hz _ ha).1 (hz _ hh).1 ht
  have hw : amount r l * amount r s= r^(4+(L.degree+S.degree)) := by
    dsimp only [amount, l,s,rooted]; rw [← pow_add];congr 1;omega
  let v := amount r l * amount r s
  have ha : ‖v * mourn (gesture l) (gesture s) K-gleam L S g‖ ≤ bill (-4) (clim A (ζ k)) := by
    have hh : v*gleam l s M=gleam L S g := Eq.trans (b:=v*gleam l s (r • g)) (by unfold g; rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul]) (grown l s hs g hq)
    rw [← hh,← mul_sub,norm_mul, Real.norm_of_nonneg (show 0≤ v by unfold v; rw [hw]; positivity)]
    apply (mul_le_mul_of_nonneg_left hv (show 0≤v by unfold v; rw [hw]; positivity)).trans; dsimp only [v]
    rw [hw,←mul_assoc]; exact hu p M he hx
  refine ⟨hq,ha, le_trans (show ‖v * _‖ ≤ ‖v* mourn (gesture l) (gesture s) K-gleam L S g‖+ ‖gleam L S g‖ from ?_) ?_⟩
  · generalize v*mourn (gesture l) (gesture s) K=z; exact le_trans (le_of_eq (congr_arg norm (sub_add_cancel z _).symm)) (norm_add_le ..)
  have hz : bill (-4) (clim A (ζ k)) ≤ 1 := by grw [billed _ (by norm_num : (-4:ℝ) ≤ 0)]; rw [bill_zero]
  apply (add_le_add (ha.trans hz) Ht).trans; rw [add_comm 1 C]; exact hl


lemma chamber_nowX (d : ℕ) (h : G.Simple) (β e : ℝ) (he : 0<e) (hB : 6 ≤ β) {x : Points n} (hx : x∈conf n) (ζ : ℕ→ℕ) (hz:Tendsto ζ atTop atTop)(px:ℕ → Points n)(zφ:Tendsto (fun i=> tested A β (ζ i) (px i)) atTop (𝓝 x)) : ∀ᶠ k in atTop,
    ∀ p H, Model A d (ζ k) p H → ∀ i j,i ≠ j → MeridianArc A (bill e (clim A (ζ k))) (bill (-4) (clim A (ζ k))) (mag A β (ζ k)) (wood A (ζ k)) d (ζ k) p
       (choose A β (ζ k) (px k) i) (choose A β (ζ k) (px k) j) (tested A β (ζ k) (px k) i) (tested A β (ζ k) (px k) j) H := by
  have Hx : ∀ᶠ k in atTop, ∀ i j, ∀ u v : Hub G (d+2) 0, i≠j →
      ∀ p H, Model A d (ζ k) p H → ∀ X Y,
        let l:=rooted u.val X; let s:=rooted v.val Y
        let f:= choose A β (ζ k) (px k); let K := looked (H.κ (ζ k)) (f i) (f j)
        let r:=mag A β (ζ k); let M:=moved (px k) A β i j (ζ k) X Y
        attends d (wood A (ζ k)) l→ attends d (wood A (ζ k)) s→ r⁻¹ • M ∈ away ∧
          ‖amount r l*amount r s*mourn (gesture l) (gesture s) K - gleam l s (r⁻¹ • M)‖ ≤ bill (-4) (clim A (ζ k)) ∧
            ‖amount r l * amount r s*mourn (gesture l) (gesture s) K‖ ≤ bill e (clim A (ζ k)) := by
    refine eventually_all.mpr (fun (i : Fin n) => eventually_all.mpr fun j => eventually_all.mpr fun u => eventually_all.mpr fun v => ?_)
    by_cases he' : i=j
    · exact Eventually.of_forall fun k H => False.elim (H he')
    refine (scaledX A x i j ((show Injective x.ofLp from hx).ne he') β e he hB u.val v.val h ζ hz px zφ).mono fun k hf hv p H hp X Y => hf p d H hp X Y
  filter_upwards [Hx] with k hk p H hp i j hij
  let f:= choose A β (ζ k) (px k); let z:=tested A β (ζ k) (px k); let r:= mag A β (ζ k)
  have he (L) (h : attends d (wood A (ζ k)) L) : (rooted (G:=G) L 0).degree+2 ≤ d+2 := by
    unfold rooted; rcases h with ⟨_,ht⟩|⟨he,hl⟩ <;> dsimp only <;> omega
  let U (L : Degree G) (h) : Hub G (d+2) 0 := ⟨{ L with point:=0},rfl,Nat.zero_le _,he L h⟩
  refine ⟨hp.1 _ _, fun L S hX hY => ?_, fun a b => ?_⟩
  · have hL := hk i j (U L hX) (U S hY) hij p H hp L.point S.point hX hY |>.2.2
    change ‖amount r L*amount r S*mourn (gesture L) (gesture S) _‖ ≤ _ at hL
    rw [norm_mul,norm_mul, Real.norm_of_nonneg (show 0≤amount r L from (pow_pos (mag_pos A ..) _).le), Real.norm_of_nonneg (show 0 ≤ amount r S from (pow_pos (mag_pos A ..) _).le)] at hL
    exact hL
  have ha : attends d (wood A (ζ k)) a.val := Or.inl ⟨a.property.1,a.property.2.2⟩
  have hb : attends d (wood A (ζ k)) b.val := Or.inl ⟨b.property.1,b.property.2.2⟩
  have hw := hk i j (U a.val ha) (U b.val hb) hij p H hp a.val.point b.val.point ha hb
  let M:= moved (px k) A β i j (ζ k) a.val.point b.val.point
  have hm : r⁻¹ • M = z i-z j := by unfold M; rw [settled, a.property.1,b.property.1, sub_self, smul_zero,add_zero]
  have ht : z i≠z j := sub_ne_zero.mp (show z i-z j ∈ away from hm ▸ hw.1)
  rw [← glisten a.val b.val (z i) (z j) ht,← hm]; exact hw.2.1
end YM.Next.Rank.Wall
