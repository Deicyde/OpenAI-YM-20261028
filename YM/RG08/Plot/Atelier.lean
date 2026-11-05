import YM.RG08.Plot.Choice
/-!
# Cost projection across root counts. No repeated loss in entry norms.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Plot
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I J α Y:Type}{L e h D j k r:ℕ}{X:Chain}{v a ℓ:I→ℕ}{x:I→E4}{u:I→Cover}{c A v' η p q w y δ:I→ℝ}{R:ℝ}{G:Gauge}
section volume
variable {β:I→Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y]
def Club (s:I→ Finset α):= (i:I) × {j // j∈s i}
lemma Card.club {s:I→Finset α}{V: ∀ i:I, α→ Rooted Y (β i) r} (HΞ:Audience y)(hA:0≤p)(hq:0 ≤ η)(h:Card k (fun i:Club s=> y i.1) (fun i:Club s=> p i.1) (fun t:Club s=> V t.1 t.2.val) (fun t:Club s=>η t.1)): Card k y (fun i=> (↑((s i).card):ℝ)*p i) (fun i=>∑ j∈s i, V i j) η:= by
    obtain ⟨A,⟨B,v,hB,H⟩,hQ⟩:=h.money -- need Audience y for contraction
    let C i:=max 0 (B*y i^v)
    -- if F card=0 budget p no sign; but V s may empty. need audience y
    have hC := Weighed.power y HΞ v -- add
    refine ⟨_,(Weighed.constant y hB).times hC,fun i=>?_⟩
    let t j (hj:j∈s i):Club s:=⟨i,j,hj⟩
    have ht j (hj:j∈s i): cis k (η i) (V i j) ((B*y i^v)*p i):= Ink.raise (hQ (t j hj)) (mul_le_mul_of_nonneg_right (H (t j hj)|>.2) (hA _))
    refine Ink.raise (Ink.additions ht (zero_le_one.trans (tailp (hq i)))) (le_of_eq ?_); rw [sum_const,nsmul_eq_mul]; change _=(B*y i^v)*(↑_ *p i); ring
lemma Drum.club {s:I→Finset α}{V W: ∀ i:I, α→Rooted Y (β i) r}(he: Audience y)(hδ:0≤δ)(hp:0≤p)(hq:0≤η)(h:Drum k (fun i:Club s=>y i.1) (fun i=>δ i.1) (fun i=>p i.1) (fun t=>V t.1 t.2.val) (fun t=>W t.1 t.2.val) (fun t=>η t.1)): Drum k y δ (fun i=> (↑((s i).card):ℝ)*p i) (fun i=> ∑ j∈s i,V i j) (fun i=>∑ j∈s i,W i j) η:= by
   refine ⟨Card.club he hp hq h.first,Card.club he hp hq h.second,?_⟩
   let t:=(fun i=>∑ j∈s i,V i j)-(fun i=>∑ j∈s i,W i j)
   have hz: t=(fun i=>∑ j∈s i,(V i j-W i j)):= funext fun i=>(Finset.sum_sub_distrib ..).symm
   unfold t at hz; rw [hz,show (δ*(fun i=> (↑((s i).card):ℝ)*p i)) = (fun i=> (↑((s i).card):ℝ)*(δ*p) i) from funext fun _=>mul_left_comm ..]; exact Card.club (V:=fun i j=> V i j-W i j) he (fun i=>mul_nonneg (hδ i) (hp i)) hq h.funds
lemma Drum.loosen {U F: ∀ i:I,Rooted Y (β i) r}(h:Drum k y δ p U F η)(he:p≤w)(hp:0≤δ): Drum k y δ w U F η:= ⟨h.first.raise he,h.second.raise he,h.funds.raise fun i=>mul_le_mul_of_nonneg_left (he i) (hp i)⟩
lemma Drum.cheap {V F:∀ i:I,Rooted Y (β i) r}(h:Drum k y δ (p*q) V F η)(he:Weighed y p): Drum k y δ q V F η := ⟨Run.Card.lesser h.first he,Run.Card.lesser h.second he,by have ht:= h.funds; rw [mul_left_comm δ p] at ht; exact Run.Card.lesser ht he⟩
end volume
section payments
variable {V F:I→ BoardU D R G} {g:I→ Profile D}{φ:I→Exam D}
def WidthP (X:Chain)(a ℓ:I→ℕ)(i:I):= spanP X (a i) (ℓ i)
local notation "◾" => WidthP X a ℓ
lemma bite (h:Card k y δ (fun i=>V i e r) 1) (hp:0≤A)(hx:∀ i,Reads (φ i) (A i)): Card k y (δ*A) (fun i=> ringU (φ i) (V i) e r) 1 := by
    obtain ⟨B,hB,H⟩:=h.money; refine ⟨_,hB,fun i=> Ink.raise (slot_budget _ (H i) zero_le_one (hx i) (hp i)) (le_of_eq ?_)⟩; rw [Pi.mul_apply]; ring
lemma fingers (h:Drum k y δ p (fun i=> V i e r) (fun i=> F i e r) 1)(hp:0≤A)(hx:∀ i,Reads (φ i) (A i)): Drum k y δ (p*A) (fun i=>ringU (φ i) (V i) e r) (fun i=>ringU (φ i) (F i) e r) 1:= by
    refine ⟨bite h.first hp hx,bite h.second hp hx,?_⟩
    rw [←mul_assoc, show (fun i=>ringU (φ i) (V i) e r)-(fun i=>ringU (φ i) (F i) e r)= (fun i=>ringU (φ i) ((V-F) i) e r) from funext fun i=>funext fun j=>Eq.symm (_root_.map_sub (plug (φ i) R) (V i e r j) (F i e r j))]; exact bite (V:=V-F) h.funds hp hx
lemma permit_pos (h:ℕ)(i:I):0≤ tariff h (◾ i):= div_nonneg (pow_nonneg (spanP_pos ..).le _) (pow_nonneg (spanP_pos ..).le _)
lemma colorUp (h:Drum k y δ p (fun i=> V i e r) (fun i=>F i e r) 1)(hp:0≤A)(hx:∀ i,Reads (φ i) (A i))(he:◾ ≤1)(x:I→E4)(u:I→Cover)(n:ℕ): Drum k y δ (fun i=> p i*A i*tariff n (◾ i)) (fun i=>unitA X n (a i) (ℓ i) (φ i) (x i) (V i) (u i) e r) (fun i=>unitA X n (a i) (ℓ i) (φ i) (x i) (F i) (u i) e r) 1:= by
   let φ' i:=exteriorP (φ i) (◾ i) (x i) (u i); let q i:=tariff n (◾ i)
   have hz:= fingers (φ:=φ') h hp (fun i=> reads_roll (hx i) (spanP_pos ..).le (he i))
   let P i:= ringU (φ' i) (V i) e r; let B i:= ringU (φ' i) (F i) e r
   have hw(Y:I→Shale (Loc G 1) r)(w:I→ℝ)(h: Card k y w Y 1): Card k y (w*q) (fun i=>q i • Y i) 1:= by
     obtain ⟨Q,hQ,H⟩:=h.money; refine ⟨_,hQ,fun i=> Ink.raise (Ink.scale (H i) _) ?_⟩; rw [Real.norm_of_nonneg (show 0≤q i from permit_pos n i)]; exact (by rw [Pi.mul_apply]; exact le_of_eq (by ring))
   refine ⟨hw _ _ hz.first,hw _ _ hz.second,?_⟩
   change Card k y (δ*(p*A*q)) ((fun i=> q i • P i)-(fun i=>q i • B i)) 1; rw [← mul_assoc,show (fun i=> q i • P i)-(fun i=> q i • B i)=(fun i=> q i • ((P-B) i)) from funext fun i=> (smul_sub ..).symm]; exact hw _ _ hz.funds
lemma summited (hD:0≤R)(hp:Audience y)(h:Weighed y v')(he:∀ i, Spatial (g i).val (v' i))(hx:∀ i,u i∈ blush (g i) X (a i) (ℓ i) (x i) R)(hv:◾ ≤1): Weighed y (fun i=> ◾ i*size (u i-arcT X (a i) (ℓ i) (x i))) := (((Weighed.constant y (show 0≤(4:ℝ) by norm_num)).times ((Weighed.constant y (show 0≤(2+R:ℝ) by positivity)).plus h hp))).mono (fun i=>mul_nonneg (spanP_pos ..).le (Nat.cast_nonneg _)) (fun i=> native_fee (g i) _ _ _ _ _ _ (h.positive _) hD (he i) (hv _) _ (hx i))
lemma posted (h: Weighed y v')(hp:0≤R)(hx:∀ i,Spatial (g i).val (v' i))(he:◾ ≤1)(hv:Audience y)(x:I→ E4): Weighed y (fun i=> ((blush (g i) X (a i) (ℓ i) (x i) R).card:ℝ)*(◾ i)^4):= by
   apply (((((Weighed.constant y (show 0≤(2:ℝ) by norm_num)).times ((Weighed.constant y (show 0≤(2+R:ℝ) by positivity)).plus h hv))).plus Weighed.one hv).powers 4).mono (fun i=>mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (spanP_pos ..|>.le) _))
   intro i; refine le_trans (le_of_eq (mul_comm _ _)) (blush_count (hx i) (h.positive _) hp (show spanP X (a i) (ℓ i)≤1 from he i))
lemma profile_s (hD:0≤R)(hY:Audience y)(hz:0≤p)(hq:0≤δ)(hv:Weighed y v')(he:∀ i,Spatial (g i).val (v' i))(h:Drum k y δ p (fun i=> V i e r) (fun i=> F i e r) 1)(hp:0≤A)(hx:∀ i,Reads (g i).val (A i))(hm:◾≤1)(x:I→E4)(n:ℕ) :
   Drum k y δ (fun i=>p i*A i / (◾ i)^n) (fun i=> (Town.season (-arcT X (a i) (ℓ i) (x i)) (collect X n (a i) (ℓ i) (g i) (x i) (V i))) e r) (fun i=> (Town.season (-arcT X (a i) (ℓ i) (x i)) (collect X n (a i) (ℓ i) (g i) (x i) (F i))) e r) (fun i=>◾ i):= by
    let P i:= blush (g i) X (a i) (ℓ i) (x i) R; have hP:= posted hv hD he hm hY x
    simp only [move_collect,Finset.sum_apply]
    let projectW (i:Club P): I:=i.1; let p' i:= p i*A i*tariff n (◾ i); have hz':0≤p':=fun i=>mul_nonneg (mul_nonneg (hz _) (hp _)) (permit_pos ..)
    let Z (U:I→BoardU D R G)(i:I)(u:Cover): Shale (Loc G 1) r:= (Town.season (u-arcT X (a i) (ℓ i) (x i)) (unitA X n (a i) (ℓ i) (g i).val (x i) (U i) u)) e r
    apply Drum.cheap (p:=fun i:I=> (↑(P i).card:ℝ)*(◾ i)^4) _ hP
    rw [show (fun i:I=> (↑(P i).card:ℝ)*(◾ i)^4)*(fun i=> p i*A i/(◾ i)^n)=(fun i=>(↑(P i).card:ℝ)*p' i) from funext fun i=>by unfold p' tariff; change (↑(P i).card:ℝ)*(◾ i)^4*(p i*A i/(◾ i)^n)=_; ring]
    let Q':=(fun i:Club P=> X.S.a (a (projectW i))) -- use
    apply Drum.club (s:=P) (V:=Z V) (W:=Z F) hY hq hz' (fun i=>(spanP_pos ..).le) -- fix space
    let R':=fun i:Club P => i.2.val
    have hh:(WidthP X (fun i=>a (projectW i)) (fun i=>ℓ (projectW i))) ≤1:= fun i=>hm (projectW i)
    apply roam_enough (b:=0) (colorUp (e:=e) (φ:=fun i:Club P=>(g (projectW i)).val) (a:=fun i=>a (projectW i)) (h.mold projectW) (A:=fun i=> A (projectW i)) (fun i=>hp _) (fun i=> hx _) hh (fun i=> x (projectW i)) R' n) (fun i=>(spanP_pos X (a (projectW i)) (ℓ (projectW i))).le) hh (z:=fun i:Club P=> R' i-arcT X (a (projectW i)) (ℓ (projectW i)) (x (projectW i))) (summited (g:=fun i:Club P=>g (projectW i)) hD (fun i=>hY _) (hv.transfer projectW) (fun i=>he _) (fun i=>i.2.property) hh) (fun i=>hY _)
end payments
end YM.RG08.Plot
