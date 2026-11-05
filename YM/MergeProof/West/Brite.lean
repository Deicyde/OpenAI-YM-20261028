import YM.MergeProof.West.Cream
import YM.MergeProof.West.Dol
import YM.Next.RANK.Promises

set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Wall
open Function Set Lattice Wilson RG Normal Perch Prayer  Atlas Station CellsInt Configuration Glimmer Filter Beamer Maxwell
open scoped Topology BigOperators Classical

variable {G : Gauge} (A : Levels G) {k n d : ℕ}

private lemma thump {z s r : ℝ} (hr : 0<r) (hz : 1≤z) (hs : r*z^2 ≤ s) (L : Degree G) : amount r L*z^4 ≤ amount s L := by
  unfold amount; apply le_trans _ (pow_le_pow_left₀ (mul_nonneg hr.le (sq_nonneg _)) hs _); rw [mul_pow, ← pow_mul];
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (by omega)) (pow_nonneg hr.le _)

private lemma bled (x y : Degree G) {d : ℕ} {r : ℝ} (z : KeyIn G d → KeyIn G d→ℝ) (h : x.degree=d-1 ∨ y.degree=d-1) :
    mourn (gesture x) (gesture y) (arc d r z)=0 := by
  unfold arc; simp_rw [map_sum,map_smul]; refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have ht (x v) (u : KeyIn G d) : v=x.degree → v=d-1 → gesture x (arbor d r u) = 0 := by
    intro hx h; rw [arbor,map_smul,tester,gesture_over,smul_zero]; have hh := u.property; unfold Labels.generation at hh;omega
  rw [show mourn (gesture x) (gesture y) (fun s t => arbor d r i s*arbor d r j t)=gesture x (arbor d r i)*gesture y (arbor d r j) from ?_]; rotate_left
  · change gesture x (fun s => gesture y (arbor d r i s • arbor d r j)) = _
    rw [show (fun s => gesture y (arbor d r i s • arbor d r j))= (gesture y (arbor d r j)) • arbor d r i from funext (fun s => (map_smul ..).trans (mul_comm ..)),map_smul]; exact mul_comm ..
  cases h with
  | inl h => rw [ht x _ i rfl h,zero_mul,smul_zero]
  | inr h => rw [ht y _ j rfl h,mul_zero,smul_zero]
private lemma order (x : Degree G) {d m : ℕ} (h : attends d m x) : x.degree ≤ d-1 := by rcases h with ⟨he,hp⟩|⟨he,hp⟩ <;> omega
private lemma attend (L : Hub G d 0) (n : ℕ) : attends d n L.val := Or.inl ⟨L.property.1,L.property.2.2⟩

theorem on_hold {x : Points n} (b : ℝ) (D d : ℕ) (H : G.Simple) (hx : x∈conf _) (hb : 6≤ b) (ζ : ℕ→ℕ) (hz:Tendsto ζ atTop atTop)(px:ℕ → Points n)(zφ:Tendsto (fun i=> tested A b (ζ i) (px i)) atTop (𝓝 x)) :
    ∀ᶠ k in atTop,∀ h : Fit A b (ζ k) (px k), Allowed A b (ζ k) → ∀ p F,Vantage A d (ζ k) p n D b F → Bell A F d D h := by
  let e := fuel D n
  have he : 0<e := fuel_real D n
  have hE : e≤1/4 := by dsimp only [e,fuel]; apply div_le_div_of_nonneg_left zero_le_one (by norm_num); push_cast;nlinarith
  have ht : -4+3*(e/4)< -3 := by linarith
  filter_upwards [chamber_nowX A d H b (e/8) (by positivity) hb hx ζ hz px zφ, penaltyX x hx b d A H (by linarith) ζ hz px zφ,
    ((hat_rate A H).comp hz).eventually (transports (show -4+3*(e/4)< -3 from ht) 3),
    ((hat_rate A H).comp hz).eventually (transports (show e/8 < e/4 by linarith) 2)] with k hS hQ t₀ t₁
  dsimp only [Function.comp_apply] at t₀ t₁
  intro h ha p F hr
  obtain ⟨hM,hL⟩ := hr
  refine ⟨fun i j => hL.colors _ _ _,fun u hu z => ?_,fun u hu => ⟨fun i => ?_,fun i j => ?_⟩⟩
  · change (( (_ : ℂ).re:ℝ) : ℂ)= _; rw [hL.sends_mean]; simp
  · let l:=middle A b (ζ k); let g:= choose A b (ζ k) (px k); let c:= clim A (ζ k); let s:=stretch A b (ζ k)
    let m:= A.clock.monitor (ζ k); have hm : 1 ≤ m := Real.one_le_exp (sq_nonneg _)
    let a:= mag A b (ζ k); have hp : 0 < a := mag_pos ..
    let P:=fraction n D c; have hC : 0 ≤ P := (Real.exp_pos _).le; have h3 := ha.dilation
    let H:= Wall.field F (before A b (ζ k)) (g i) u
    have hP : 0<s := div_pos (A.S.a_pos l) (A.S.a_pos _)
    rw [show μre A.S F (choose A b (ζ k) (px k)) (before A b (ζ k)) _ i=H by
      funext z; unfold μre; rw [hL.sends_mean]; rfl]
    have he (L : Degree G) (H' : attends d (wood A (ζ k)) L) : amount a L*‖gesture L H‖ ≤ Perch.bill (-3) c := by
      have hk : m^4*(amount a L* ‖gesture L H‖) ≤ P^2 := by
        have he := mul_le_mul_of_nonneg_right (thump hp hm h3 L) (norm_nonneg (gesture L H))
        rw [← mul_assoc,mul_comm (m^4)]
        exact he.trans (hL.dawn (g i) u L (order L H') hP hC hu.1)
      apply le_of_mul_le_mul_left _ (a:=m^4) (pow_pos (zero_lt_one.trans_le hm) _); apply hk.trans
      change bill _ _ ^ _ ≤ _
      rw [show m=bill 1 c from fire_bill A (ζ k),bills,bills,overlap]; apply billed; push_cast; linarith
    refine ⟨⟨hL.preserve u hu.2 (g i),fun L H' => (he L H').trans (billed _ ?_)⟩, fun L => he _ (attend _ _)⟩
    exact le_trans (by norm_num : (-3:ℝ)≤0) (by change 0≤e/4; linarith)
  let g := choose A b (ζ k) (px k); let K:= currentX (Ship.fitting h) G d; let a := mag A b (ζ k); let l:= middle A b (ζ k); let s:=stretch A b (ζ k)
  let L:= looked (scope (lines F l (before A b (ζ k))) (F.κ l)) (g i) (g j)
  let p₀:= A.clock.monitor (ζ k); let c:= clim A (ζ k); let P₀:= bill (e/4) c
  let B:= bill (-4+3*(e/4)) c; let δ:= bill (-3) c
  have ht := hL.moth (g i) (g j); have hl : 0<s := div_pos (A.S.a_pos l) (A.S.a_pos _)
  have h₁ : 1≤p₀ := Real.one_le_exp (sq_nonneg _); have hC : 0 ≤ P₀ := (Real.exp_pos _).le
  have h₂ : 0<a := mag_pos ..; have he₂ : 0 < p₀^4 := pow_pos (zero_lt_one.trans_le h₁) _
  have he₁ : δ ≤ P₀ := billed _ (by linarith)
  have hE (x : Degree G) : 0 < amount a x := pow_pos h₂ _
  have Hk (x y : Degree G) (hx : attends d (wood A (ζ k)) x) (hy : attends d (wood A (ζ k)) y) :
      amount a x * amount a y * ‖mourn (gesture x) (gesture y) L‖ ≤ B := by
    have hs : a*p₀^2 ≤ s:= ha.dilation
    apply le_of_mul_le_mul_left _ (pow_pos (zero_lt_one.trans_le h₁) 4)
    calc
      _ = amount a x*p₀^4 * amount a y * _ := by ring
      _ ≤ amount s x* amount s y * ‖mourn (gesture x) (gesture y) L‖ := mul_le_mul_of_nonneg_right (mul_le_mul (thump h₂ h₁ hs x)
          ((le_mul_of_one_le_right (hE y).le (one_le_pow₀ h₁)).trans (thump h₂ h₁ hs y)) (hE y).le (pow_nonneg hl.le _)) (norm_nonneg _)
      _ ≤ P₀^3 := hL.dusk (g i) (g j) _ _ (order _ hx) (order _ hy) hl hC
      _ = _ := by dsimp only [P₀,B]; rw [show p₀=bill 1 c from fire_bill A (ζ k),bills,bills,overlap]; push_cast; ring_nf
  rw [called F]; by_cases hy : i=j
  · subst j; rw [if_pos rfl]; subst L
    have hz : collect d (Ship.fitting h) a G i i=0 := by
      unfold collect arc; simp only [dies,Complex.zero_re,zero_smul, Finset.sum_const_zero]
    rw [hz,sub_zero]; have hB : B ≤ δ := billed c (by linarith)
    let L:= looked (scope (lines F l (before A b (ζ k))) (F.κ l)) (g i) (g i)
    have ho (x y : Degree G) (hx : attends d (wood A (ζ k)) x) (hy : attends d (wood A (ζ k)) y) : amount a x*amount a y*‖mourn (gesture x) (gesture y) (0-L)‖≤δ := by rw [zero_sub,map_neg,norm_neg]; exact (Hk x y hx hy).trans hB
    exact ⟨fun i => (signal G).sub_mem (signal G).zero_mem (ht.1 i),fun i => (signal G).sub_mem (signal G).zero_mem (ht.2 i),fun x y H H' => (ho x y H H').trans he₁, fun x y => ho _ _ (attend ..) (attend ..)⟩
  rw [if_neg hy]
  let a' := looked (F.κ (ζ k)) (g i) (g j)
  let s' := collect d (Ship.fitting h) a G i j
  let C:= fun s t=> (K.cov (i,s) (j,t)).re
  have hv := hS p F hM i j hy
  have hs (X y : Hub G d 0) :
      amount a X.val * amount a y.val * ‖mourn (gesture X.val) (gesture y.val) (a'-L-s')‖ ≤ δ := by
    let f:= mourn (gesture X.val) (gesture y.val)
    let c' := amount a X.val * amount a y.val
    have hc' : 0 ≤ c' := mul_nonneg (hE _).le (hE _).le
    let M:= Prayer.light X.val y.val (tested A b (ζ k) (px k) i) (tested A b (ζ k) (px k) j)
    have he : ‖c' * f a'-M‖≤bill (-4) c := hv.origin X y
    have ha : ‖c'*f s'-M‖≤bill (-4) c := hQ h i j X y hy
    have he' : c'*‖f L‖ ≤ B := Hk _ _ (attend ..) (attend ..)
    change c'*‖f _‖ ≤ _; calc
      _ = ‖((c'*f a'-M)-(c'*f s'-M))-c'*f L‖ := by rw [map_sub,map_sub,show (c'*_-M)-(c'*_-M)-c'*_ = c'*(f a'-f L-f s') by ring,norm_mul, Real.norm_of_nonneg hc']
      _ ≤ _ := by
        apply (norm_sub_le ..).trans
        apply (add_le_add ((norm_sub_le ..).trans (add_le_add he ha)) ((by rw [norm_mul, Real.norm_of_nonneg hc']; exact he') : ‖c'*f L‖ ≤ B)).trans
        have hr : bill (-4) c ≤ B := billed _ (by linarith); linarith only [hr,t₀]
  refine ⟨fun i => (signal G).sub_mem ((signal G).sub_mem (hv.closures.1 i) (ht.1 i)) (choke d a C i),
    fun i => (signal G).sub_mem ((signal G).sub_mem (hv.closures.2 i) (ht.2 i)) (chokes d a C i), ?_, hs⟩
  intro x y he hk
  by_cases hh : (x.degree+2 ≤ d ∧ x.point=0) ∧ (y.degree+2 ≤ d ∧ y.point=0)
  · exact (hs ⟨x,hh.1.2,Nat.zero_le _,hh.1.1⟩ ⟨y,hh.2.2,Nat.zero_le _,hh.2.1⟩).trans he₁
  have hb' : x.degree=d-1 ∨ y.degree=d-1 := (not_and_or.mp hh).elim (fun H => Or.inl ((he.resolve_left (fun ⟨a,b⟩ => H ⟨b,a⟩)).1)) (fun H => Or.inr ((hk.resolve_left (fun ⟨a,b⟩ => H ⟨b,a⟩)).1))
  let t := amount a x * amount a y
  change t * ‖mourn _ _ (a'-L-s')‖≤P₀
  rw [map_sub,show mourn (gesture x) (gesture y) s'=0 from bled x y C hb', sub_zero, map_sub]
  apply le_trans (mul_le_mul_of_nonneg_left (norm_sub_le ..) (show 0≤t from mul_nonneg (hE _).le (hE _).le))
  rw [mul_add]
  have hU : B ≤ bill (e/8) c := billed _ (by linarith)
  apply (add_le_add (hv.extent x y he hk) (Hk x y he hk)).trans; linarith only [hU,t₁]
end YM.Next.Rank.Wall
