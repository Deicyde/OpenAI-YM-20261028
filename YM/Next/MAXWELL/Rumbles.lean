import YM.Next.MAXWELL.Frenzy

/-! # Free vertex echo -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} {j k l n r M d : ℕ}

private lemma eat_front {x : Points (n+1)} (H : x∈conf _) (p : Probe G j) (P : WickPol G) (v : Fin n → WickPol G) :
    moment G x (Fin.cons (α:=fun _ => WickPol G) (symbol j p * P) v) = ∑ i : Fin n,
      moment G x (Fin.cons (α:=fun _ => WickPol G) P (update v i (eat p (x 0) (x i.succ) (v i)))) := by
  let W := Fin.cons (α:=fun _ => WickPol G) P v
  rw [show Fin.cons (α:=fun _ => WickPol G) (symbol j p*P) v=update W 0 (symbol j p*W 0) from (Fin.update_cons_zero ..).symm,moment_one _ W _ H]
  let f i := moment G x (update W i (eat p (x 0) (x i) (W i)))
  change ∑ i ∈ Finset.univ.erase 0, f i=_
  have hi : (∑ i∈Finset.univ.erase 0, f i) = ∑ i : Fin n, f i.succ := by
    apply add_right_cancel (b:=f 0)
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ _), Fin.sum_univ_succ]; exact add_comm ..
  rw [hi]; apply Finset.sum_congr rfl; intro i _; unfold f; congr 1
  exact (Fin.cons_update ..).symm

lemma front_egress {x : Points n} {y : E4} (H : Points.cons y x∈conf _) (hx : x∈conf _) (p : Probe G k) (q : Probe G l) (v : Fin n→WickPol G) :
    bookend x y v (symbol k p * symbol l q)=∑ i : Fin n,∑ j : Fin n,
      wield (wield (moment G x) j (eat q y (x j)).toLinearMap) i (eat p y (x i)).toLinearMap v := by
  rw [book_eval,eat_front H p (symbol _ q)]; apply Finset.sum_congr rfl; intro i _
  let C := Points.cons y x
  let W := update v i (eat p y (x i) (v i))
  change moment G C (Fin.cons _ W)=_
  have he := eat_front H q 1 W; rw [mul_one] at he
  rw [he]
  apply Finset.sum_congr rfl; intro j _; rw [← adjoin hx, wield_at,wield_at]; rfl

private lemma cluster_in {x : Points (n+1)} (hx : x∈conf _) (z : E4) (hz : z∈away) :
    ∀ᶠ t in little,Points.cons (x 0+t • z) x∈conf _ := by
  have he : Tendsto (fun t : ℝ => x 0+t • z) little (𝓝 (x 0)) := by
    simpa only [id_eq, zero_smul, add_zero] using! tendsto_const_nhds (x := x 0) |>.add ((show Tendsto id little (𝓝 (0:ℝ)) from tendsto_id.mono_left nhdsWithin_le_nhds).smul_const z)
  have hh (i : Fin n) : ∀ᶠ t in little,x 0+t • z≠x i.succ := he.eventually (isOpen_ne.mem_nhds ((show Injective x.ofLp from hx).ne (Ne.symm (Fin.succ_ne_zero i))))
  filter_upwards [eventually_all.mpr hh,self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht hy
  have hp (i) : x 0+t • z≠x i := by
    refine Fin.cases ?_ ht i; intro hw
    exact smul_ne_zero (show t≠0 from (show t>0 from hy).ne') (show z≠0 from hz) (add_eq_left.mp hw)
  intro i j; refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases (fun _ => rfl) (fun j h => ?_) j; exact ((hp j) h).elim
  exact Fin.cases (fun h => ((hp i) h.symm).elim) (fun k h => congr_arg Fin.succ (hx h)) j

/-- Vertex lemma. -/
lemma vertex {x : Points (n+1)} (hx : x∈conf _) (p : Probe G k) (q : Probe G l) (hK : l<k) (P : WickPol G)
    (hp : P∈shelf G j) (v : Fin n→ WickPol G) (M : ℕ) (hr : 8+k+l+j+j<M) :
    Deep (4+k+j) M (fun z => bookend x (x 0+z) (Fin.cons (α:=fun _ => WickPol G) P v) (symbol k p*symbol l q))
      (fun z=> moment G x (Fin.cons (α:=fun _ => WickPol G) (symbol l q * singleBite j p z P) v)) := by
  classical
  let r := 4+k+j
  let W := Fin.cons (α:=fun _ => WickPol G) P v
  let P' := moment G x
  let B z i := (eat p (x 0+z) (x i)).toLinearMap
  let C z i := (eat q (x 0+z) (x i)).toLinearMap
  let F (i b : Fin (n+1)) (z:E4) := wield (wield P' b (C z b)) i (B z i) W
  let K (i b : Fin (n+1)) (z:E4) := if i=0 ∧ b≠0 then wield (wield P' b (C 0 b)) 0 (singleBite j p z).toLinearMap W else 0
  have hG {i : Fin (n+1)} (hi : i≠0) : x 0 ≠ x i := (show Injective x.ofLp from hx).ne hi.symm
  have he (i b : Fin (n+1)) : Deep r M (F i b) (K i b) := by
    by_cases h : i=0
    · subst i; by_cases hb:b=0
      · subst b; rw [show K 0 0=0 from funext fun z => if_neg (by simp)]
        let Q := P'.toLinearMap W 0
        have hh : F 0 0=(fun z => Q (eat q (x 0 + z) (x 0) (eat p (x 0+z) (x 0) P))) := by
          ext1 z; unfold F; rw [wield_zero_dep,wield_at]; rfl
        rw [hh]; exact duet_path (x 0) p q Q P hp r M hr
      unfold K; simp only [hb,true_and,ne_eq,not_false_eq_true,↓reduceIte];
      exact chorus (x 0) p 0 _ (path_wield _ _ (hG hb) q b (fun _ => P') (fun _ => continuousAt_const)) W (show _ from hp)
    rw [show K i b=0 from funext fun z => if_neg (by simp [h])]
    by_cases hb:b=0
    · subst b
      unfold F; simp_rw [wield_switch P' 0 i (Ne.symm h) (C _ 0)]
      exact Deep.weaker (chorus (M:=M) (x 0) q 0 _ (path_wield _ _ (hG h) p i (fun _ => P') (fun _ => continuousAt_const)) W (show _ from hp)) (by unfold r; omega)
    apply Deep.bare _ (Pole.zero _); apply Echoes.less (Echoes.regular (f:=F i b) ?_) (by unfold r; omega)
    exact path_wield _ _ (hG h) p i _ (path_wield _ _ (hG hb) q b (fun _ => P') (fun _=>continuousAt_const)) W
  refine (Deep.sum Finset.univ (fun i z => ∑ b,F i b z) (fun i z => ∑ b,K i b z) (fun i _ => Deep.sum Finset.univ _ _ (fun b _ => he i b))).congr ?_ ?_
  · intro z hz; filter_upwards [cluster_in hx z hz] with t ht; exact (front_egress ht hx p q W).symm
  intro z hz; dsimp only
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ _)]
  ·
    rw [Fin.sum_univ_succ]; simp only [K,ne_eq,Fin.succ_ne_zero, not_false_eq_true, and_self,↓reduceIte,not_true,true_and,zero_add,C,P',add_zero]
    rw [eat_front hx q (singleBite j p z P)]
    apply Finset.sum_congr rfl; intro b _
    rw [wield_at,wield_at]; congr 1
    simp only [W, Fin.update_cons_zero]
    exact (Fin.cons_update ..).symm
  intro i _ H; simp [K,H]

lemma cluster_clear {P : WickPol G} (hp : P∈shelf G j) (h : P∈ghost G d) (p : Flavor k) (q : Flavor l)
    (hk : l<k) (hd : k+l+4 ≤ d) {z : E4} (hz : z≠0) : circulate j p q (G:=G) z P∈ghost G d := by
  intro n v x hv hx
  let M := 8+k+l+j+j+1
  let R := 4+k+j
  let C' := circulate (G:=G) j p q
  let V := Fin.cons (α:=fun _ => WickPol G) P v
  have hp' : Deep R M (fun z => bookend x (x 0+z) V (team G p q)) (fun z => moment G x (Fin.cons (α:=fun _ => WickPol G) (C' z P) v)) := by
    unfold team; simp_rw [map_sum]
    have he z : moment G x (Fin.cons (α:=fun _ => WickPol G) (C' z P) v)=∑ i, moment G x (Fin.cons (α:=fun _ => WickPol G) (bit q i * singleBite j (flavor k i p) z P) v) := by
      rw [show Fin.cons (α:=fun _ => WickPol G) (C' z P) v=update (Fin.cons (α:=fun _ => WickPol G) P v) 0 (circulate j p q z P) from (Fin.update_cons_zero ..).symm,circulate_eval,MultilinearMap.map_update_sum];
      exact Finset.sum_congr rfl fun i _ => congr_arg _ (Fin.update_cons_zero ..)
    simp_rw [he]; exact Deep.sum _ _ _ (fun i hi => vertex hx _ _ hk P hp v M (by unfold M; omega))
  apply hp'.clear _ (by unfold R; omega) (show z∈away from hz)
  intro z hz; filter_upwards [cluster_in hx z hz] with t ht
  let u := x 0 + t • z
  let Y := team G p q
  rw [book_eval,exchangeSites (Equiv.swap 0 (1 : Fin (n+2))) ht]
  let s := Equiv.swap 0 (1 : Fin (n+2))
  let r := Points.rearrange s (Points.cons u x)
  let U := Fin.cons (α:=fun _ => WickPol G) Y v
  let U' := Fin.cons (α:=fun _ => WickPol G) Y V
  change moment G r (U' ∘ s) = _
  rw [show U' ∘ s=Fin.cons P U from ?_]
  · exact h _ U r (fun i => Fin.cases (team_label p q hd) hv i) (Points.rearrange_in s ht)
  ext1 i; refine Fin.cases ?_ (fun k=> ?_) i
  · simp [U',s]; rfl
  refine Fin.cases ?_ (fun i=> ?_) k
  · change U' (s 1)=Y; unfold s; rw [Equiv.swap_apply_right]; rfl
  have hw : s i.succ.succ=i.succ.succ := Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) ((Fin.succ_injective (n+1)).ne (Fin.succ_ne_zero _))
  rw [comp_apply,hw]; rfl
end YM.Maxwell.Free
