import YM.RG08.Creek.Taps
/-! # Post step bill with receipts from Bucks. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {I X J:Type}[Fintype I][DecidableEq I]{G:Gauge}{L:J→Side}{R:ℝ}{δ y w v A B C θ β σ:J→ℝ}{a:I→ℕ}{b:J→I→ℝ}{T:Finset I}{e n j r τ E D:ℕ}{P:Head I}{K M:∀ i, StripU G (L i)}
lemma weighs_man {p:X→ J→ℝ}(h: Audience y)(s: Finset X)(hp:∀ i∈s,Weighed y (p i)): Weighed y (fun i=>∑ j∈s,p j i):= by
   induction s using Finset.induction_on with
   | empty=> simp only [sum_empty]; exact Weighed.zero
   | insert i s hi ih=> simp_rw [sum_insert hi]; exact (hp i (mem_insert_self ..)).plus (ih (fun i hi=>hp i (mem_insert_of_mem hi))) h
lemma perg (h:Audience y)(hp:∀ i,0<w i)(hg:Weighed y w)(he:Weighed y (fun i=>(w i)⁻¹)) : Weighed y (shells ∘ w) := by
    have hh:= (show Weighed y (fun i=> (1+w i)/(w i)) from by simp_rw [div_eq_mul_inv]; exact (Weighed.one.plus hg h).times he)
    exact ((Weighed.constant y (show (0:ℝ)≤2 by norm_num)).times hh).powers _
lemma sticks_pay (T:Finset I)(r e n:ℕ)(h:Audience y)(hp:∀ i,0<w i)(hx:Weighed y w)(he:Weighed y (fun i=>(w i)⁻¹))(hB:Weighed y B)(hC:Weighed y C): Weighed y (fun i=>posSticks (w i) (B i) (C i) r e n T):= by
    refine Weighed.plus (Weighed.plus (((Weighed.constant y (norm_nonneg (batting r))).times hC).times hB) (weighs_man h (wheel n) (fun _ _=> weighs_man h (wheel e) (fun _ _=> weighs_man h (wheel r) (fun i _=>(Weighed.constant y (norm_nonneg (syl i.1 i.2))).times ((hC.times hC).times hB))))) h) ((Weighed.constant y (norm_nonneg (1/2:ℝ))).times (weighs_man h (partners T) (fun _ _=> weighs_man h (wheel n) fun _ _=> weighs_man h (wheel e) fun _ _=> weighs_man h (wheel r) (fun p _=>?_)))) h
    exact ((Weighed.constant y (norm_nonneg (syl p.1 p.2))).times hC).times ((hB.powers 2).times (perg h hp hx he))
lemma resp_weighed (I:Type)[Fintype I][DecidableEq I](h:Audience y)(hp:∀ i,0 < w i)(he:Weighed y w)(hx:Weighed y (fun i=>(w i)⁻¹))(hB:Weighed y B)(hC:Weighed y C): Weighed y (fun i=>resp I τ E (w i) (B i) (C i) n):= by
    induction n generalizing w with
    | zero=> exact hB
    | succ n ih=>
       let U : ℝ:= parPort I τ; have hu:0 < U:= port_pos ..; let v i:= U*w i
       have hv i:0<v i:= mul_pos hu (hp i); have hV : Weighed y v:= (Weighed.constant y hu.le).times he
       have hh:Weighed y (fun i=>(v i)⁻¹):= by simp_rw [v,mul_inv_rev]; exact hx.times (Weighed.constant y (inv_nonneg.mpr hu.le))
       have hP:= ih hv hV hh -- hB etc fixed
       exact hP.plus (weighs_man h (univ:Finset (Finset I)) fun k _=> weighs_man h (range (τ+1)) fun i _=> weighs_man h (range (E+1)) fun j _=> sticks_pay k i j n h hp he hx hP hC) h -- RESP uses base r = current v! not U*v ok
lemma chant_paid (G : Gauge)(h:Audience y)(hx:v ≤ 1)(hL:Weighed y (fun i=>(↑(L i).val:ℝ)))(hb:∀ j:I,Weighed y (fun i=> ‖b i j‖)): Weighed y (fun i=>chant_cost G (L i) (v i) n (b i)):= by
   have he:Weighed y (fun i=> Real.exp (4*v i)):= (Weighed.constant y (Real.exp_pos 4|>.le)).mono (fun i=> (Real.exp_pos _).le) (fun i=> Real.exp_monotone (mul_le_of_le_one_right (by norm_num) (hx i)))
   have hc: Weighed y (fun i=> (Fintype.card (Site (L i)):ℝ)):= by simp_rw [Lattice.site_card, Nat.cast_pow]; exact hL.powers _
   have hP(T:Finset I):Weighed y (fun i=> ‖∏ j∈T, b i j‖):=by simp_rw [norm_prod]; exact Weighed.prod T (fun j _=> hb j)
   refine weighs_man (p:=fun k i=>∑ r∈range (n+1), (Fintype.card (Site (L i)):ℝ)^ (card k)*(paid_shop (L i) k r (b i) G (v i)*Real.exp (4*v i*card k))) h (univ:Finset (Finset I)) (fun k h'=>?_)
   apply weighs_man h; intro r hr; apply Weighed.times (hc.powers k.card)
   refine Weighed.times ((((fiscal_lot (G:=G) hL h).powers r).times (he.powers r)).times (hP k)) ?_
   exact (Weighed.constant y ((Real.exp_pos (4*k.card)).le)).mono (fun i=>(Real.exp_pos _).le) (fun i=> Real.exp_monotone (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by norm_num) (hx i)) (Nat.cast_nonneg _)))
-- Consequent size. B applies EVERY input on program now with external P per-layout
variable (he:Bucks τ E y δ w v σ K M)
include he
lemma arrow_f (hB:Weighed y B): Weighed y (fun i=> arrow_all (B i) (K i) E τ):= by
   refine weighs_man (p:=fun i j=>∑ k∈range (τ+1),arrow_cost (B j) (K j) i k) he.env _ (fun i hi=> weighs_man he.env (range (τ+1)) fun k _=> weighs_man he.env (range (i+1)) fun p hp=> ?_)
   have hv := (rehearseT (e:=i-p) he.env (fun j hj=> he.castG j (by have he:=mem_range_succ_iff.mp hi; omega)) (fun i=>(he.faith i).once) (fun i=>(he.bond i).once) k p).has
   exact hv.times ((Weighed.constant y (show (0:ℝ)≤(Fintype.card (Loc G 1):ℝ)^k by positivity)).times (hB.powers k))
-- uniform K including zero orders. r all b by treble. pay w overwind lesser (advance)
lemma solar_cask {v':J→ℝ}(hv:v'≤v) : ∃ U : J→ℝ, Weighed y U ∧ ∀ i, (veiled (K i).cv).strip (v' i) (U i) ∧ (scan (K i).tree).strip (v' i) (U i) ∧ ∀ j≤ E,∀ n≤windows τ E,∀ k, Glow (Refrain (veiled (K i).cv) (K i).song none n j k) (v' i) (U i):= by
   obtain ⟨A,hA,HA⟩:=(veil_contract he.hessian he.hs).fresh.soften hv; obtain ⟨B,hB,HB⟩:=(scanned_contract he.meansT hv he.env he.hs).fresh; simp only [Pi.one_apply,mul_one] at HA HB
   choose U hu hz using fun (j:Fin (E+1)) (n:Fin (windows τ E+1)) (k: Fin (3*E+1))=> ((he.ribs j (by omega) n (by omega) k).fresh.soften hv)
   let C i:= ∑ (j: Fin (E+1)),∑ (n:Fin (windows τ E+1)), ∑ (k:Fin (3*E+1)),U j n k i
   have hC: Weighed y C:= weighs_man he.env (univ:Finset (Fin (E+1))) fun j _=> weighs_man he.env (univ:Finset (Fin (windows τ E+1))) fun n _=> weighs_man he.env (univ:Finset (Fin (3*E+1))) fun k _=> hu j n k
   refine ⟨(A+B)+C,(hA.plus hB he.env).plus hC he.env,fun i=>?_⟩
   have hP:= show A i+B i≤(A+B+C) i from le_add_of_nonneg_right (hC.positive i)
   refine ⟨strip_mono (HA i) le_rfl ((le_add_of_nonneg_right (hB.positive i)).trans hP),strip_mono (HB i) le_rfl ((le_add_of_nonneg_left (hA.positive i)).trans hP),fun j hj n hn r=> ?_⟩
   have hv' : C i ≤ (A+B+C) i:=le_add_of_nonneg_left (add_nonneg (hA.positive i) (hB.positive i)); by_cases h:r ≤ 3*E
   · let b : Fin (E+1):= ⟨j,by omega⟩; let p : Fin (windows τ E+1):=⟨n,by omega⟩; let q : Fin (3*E+1):=⟨r,by omega⟩
     apply glow_less (hz b p q i) le_rfl; rw [Pi.one_apply,mul_one]; refine le_trans ?_ hv'; exact (single_le_sum (s:=univ) (f:=fun a=>U b p a i) (fun a _=> (hu ..).positive i) (mem_univ q)).trans ((single_le_sum (s:=univ) (f:=fun a=>∑ k,U b a k i) (fun a _=>sum_nonneg fun i' _=> (hu b a i').positive i) (mem_univ p)).trans (single_le_sum (s:=univ) (f:=fun b=> ∑ n, ∑ k,U b n k i) (fun z _=>sum_nonneg fun n _=>sum_nonneg fun k _=> (hu z n k).positive i) (mem_univ b)))
   have hf:= he.faith i
   rw [not_ne_iff.mp (mt (treble_reel (n:=n) (r:=r) (e:=j) (p:=none) (veiled_whole hf.cm) hf.tune hf.lived) (fun hk=>h (by have hh:= hk.2; omega)))] ; exact glow_less (show Glow (0:Shale _ r) _ _ from Charge.zero (ling _)) le_rfl ((hC.positive i).trans hv')
lemma creek_univ (hp:∀ i,0<θ i)(ht:∀ i, advanceFee I τ (θ i) (windows τ E)≤ v i)(hx:Weighed y (fun i=>(θ i)⁻¹))(hk : ∀ i, advanceFee I τ (θ i) (windows τ E)≤(L i).val*β i) (hb:∀ j:I,Weighed y (fun i=> ‖b i j‖))(hR:1/2≤R): ∃ A:J→ℝ,Weighed y A∧∀ (i:J) (F:Layouts I G D R)(p:Head I)(a:I→ℕ), Sense a F →(∀ t, vanes a t+E ≤ τ) → Crease p→ Fest (β i) E 1 p F→ Fest (θ i) E (A i) p (creekT (K i) a (b i) F):= by
   let v' i:=advanceFee I τ (θ i) (windows τ E); have hv : θ ≤ v':= fun i=> by simpa only [v',advanceFee,pow_zero,one_mul] using advance_v I (hp i|>.le) (Nat.zero_le (windows τ E)) (t:=τ)
   obtain ⟨B,hB,HB⟩:= solar_cask he (show v'≤v from ht)
   have hX: Weighed y θ:= Weighed.one.mono (fun i=>(hp i).le) (fun i=> ((hv i).trans (ht i)).trans (he.hv i))
   have hP:=resp_weighed I he.env hp hX hx (chant_paid G he.env (show v' ≤ 1 from fun i=> (ht i).trans (he.hv i)) he.crop hb (n:=τ)) hB (n:=windows τ E) (τ:=τ) (E:=E)
   refine ⟨fun i=> creek_cost (K i) τ E (θ i) (v' i) (B i) (b i), (arrow_f he hB).times ((Weighed.constant y (Nat.cast_nonneg _)).times hP), fun i F p a hh hz h u=>?_⟩
   exact creek_fees h u hh hz (he.faith i) hR (pos_of_mul_pos_right ((hp i).trans_le ((hv i).trans (hk i))) (by positivity)) (hp i) (hB.positive i) (strip_mono (HB i).2.1 (hv i) le_rfl) le_rfl (hk i) (HB i).1 (fun j hj k hk=>(HB i).2.2 _ hk j hj) _
end YM.RG08.Creek
