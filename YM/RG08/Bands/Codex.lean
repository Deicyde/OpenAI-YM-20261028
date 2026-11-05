import YM.RG08.Bands.Beat
/-!
# First-pair forcing. Exposed pair integral across all other legs
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Bands
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town
open scoped BigOperators Topology Real ContDiff Matrix.Norms.Frobenius
variable {I α:Type}{m c:Side}{e t τ n r k:ℕ}
section op
variable [Fintype I][DecidableEq I] {F G H: Op I}{K:Matrix I I ℝ}
private lemma dance_leib (h:Fluid F)(he: Fluid G)(hp:Kᵀ=K) : landP K (dancing F G)=dancing (landP K F) G+dancing F (landP K G)+rim K F G := by
  funext n e
  have hm (b:ℕ×ℕ)(a:ℕ×ℕ) : ContDiff ℝ ω (F b.1 a.1 * G b.2 a.2):= (h _ _).mul (he _ _)
  have hv (b:ℕ×ℕ): ContDiff ℝ ω (∑ a∈wheel e,F b.1 a.1 * G b.2 a.2):= by simp_rw [Finset.sum_fn]; exact ContDiff.sum (fun i _=>hm b i)
  unfold landP rim dancing; rw [lap_sum (s:=wheel n) (h:=fun b _=>hv b)]; simp_rw [lap_sum _ (wheel e) (fun i _=>hm _ i),lap_joint _ hp (h _ _) (he _ _),sum_add_distrib]; rfl
lemma duo_gain (F X Y:Op I)(t:Finset ℕ)(h:Fluid F)(hz:Fluid Y): rim K (dancing F Y) X=dancing (rim K F X) Y+dancing F (rim K Y X):= by
   let P i:= sway (zpk (X:=I) i) F; let Q i:= sway (zpk (X:=I) i) Y; let Z i:= sway (zpk (X:=I) i) X
   have hx(i j : I): dancing (sway (zpk i) (dancing F Y)) (Z j) = dancing (dancing (P i) (Z j)) Y+dancing (dancing (Q i) (Z j)) F := by
       rw [sway_dance _ h hz,dance_plus]; unfold P Q; congr 1
       · rw [dance_rotate,dance_rotate,dance_sym Y]
       rw [dance_sym F, dance_rotate,dance_rotate,dance_sym F]
   rw [rimD,rimD,rimD]; rw [dance_sym F (∑ _, _)]; change (∑ i,∑ j: I, K i j • dancing (sway (zpk i) (dancing F Y)) (Z j)) = _
   simp_rw [hx,smul_add,sum_add_distrib,sing_a,dance_price]; rfl
lemma duo_exchange (F H:Op I)(hp:Kᵀ=K) : rim K F H=rim K H F:= by rw [rimD,rimD,sum_comm]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=> ?_; rw [show K j i=K i j from congr_fun (congr_fun hp i) j,dance_sym]
lemma duo_b (F:Op I)(h:Fluid G)(hh:Fluid H)(hp:Kᵀ=K) : rim K F (dancing G H)=dancing (rim K F G) H+dancing G (rim K F H):= by rw [duo_exchange F _ hp,duo_gain _ _ _ ∅ h hh, duo_exchange G _ hp,duo_exchange H _ hp]

def coda (K:Matrix I I ℝ)(S F:Op I):= landP K F + rim K F S
lemma coda_more (K:Matrix I I ℝ)(S:Op I)(h:Fluid F)(he:Fluid G): coda K S (F+G)=coda K S F+coda K S G:= by
    have hp : landP K (F+G)=landP K F+landP K G:= funext fun i=> funext fun j=> lap_total _ (h i j) (he i j)
    have hx (v : I→ℝ): sway v (F+G)=sway v F+sway v G:= funext fun i=>funext fun j=> Daddition _ (h _ _) (he _ _)
    simp only [coda,hp,rimD, hx,dance_plus,smul_add,sum_add_distrib]; abel
lemma coda_wash (hp:Kᵀ=K)(h: Fluid F)(he:Fluid G)(S:Op I): coda K S (dancing F G)= dancing (coda K S F) G+dancing F (coda K S G)+rim K F G := by simp only [coda,dance_leib h he hp,duo_gain F S G ∅ h he,dance_plus,dance_add]; abel
lemma drum_c (h:Fluid F)(he:Fluid G)(S:Op I) : coda K S (F-G)=coda K S F-coda K S G:= eq_sub_of_add_eq (by rw [← coda_more (F:=F-G) _ _ (fun i j=>(h i j).sub (he i j)) he,sub_add_cancel])
lemma dsp (P Q R:Op I): dancing R (P-Q)=dancing R P-dancing R Q:= eq_sub_of_add_eq (by rw [← dance_add,sub_add_cancel])
end op
section spirit
variable [Fintype α][DecidableEq α]{p: Option Side}{K:Row α α}{S:Canticle α}
def castM (X:I→HeatS α)(u:List I): HeatS α:= u.foldr (fun i p=>borne (X i) p) (upstart α)
def castF (X:I→ Screed ℝ α)(u:List I): Screed ℝ α:= u.foldr (fun i p=>gust (X i) p) (spine_one α)
def loadᵣ (a:I→ℕ)(u:List I):ℕ:= u.foldr (fun i p=>a i+p) 0
-- retain PAIRS in Γ insertion
variable {X:I→HeatS α}{F:I→Screed ℝ α}{U: HeatS α}{a:I→ℕ}{u:List I}
def junction (p:Option Side)(K:Row α α)(X:I→HeatS α)(U:HeatS α) (v:List I) : HeatS α:= match v with
   | []=>0
   | i::w=> borne (thunder p K U (X i)) (castM X w)+borne (X i) (junction p K X U w)
def pullG (p:Option Side)(K:Row α α)(X:I→HeatS α) (v:List I):HeatS α:= match v with
   | []=>0
   | i::w=> junction p K X (X i) w+borne (X i) (pullG p K X w)
omit [Fintype α][DecidableEq α] in
lemma cast_r (h:∀ i∈u, Reels (a i) (X i)): Reels (loadᵣ a u) (castM X u):= by
    induction u with
    | nil=> exact reels_start
    | cons i u ih=> exact borne_r (h i List.mem_cons_self) (ih (fun j hj=>h j (List.mem_cons_of_mem _ hj)))
omit [Fintype α][DecidableEq α] in
lemma cast_s (h:∀ i∈u, Sails (a i) (F i)): Sails (loadᵣ a u) (castF F u):= by
    induction u with
    | nil=> exact sails_start
    | cons i u ih=> exact braid_s (h i List.mem_cons_self) (ih (fun j hj=>h j (List.mem_cons_of_mem _ hj)))
lemma junction_h (h:Reels e U)(hx:∀ i∈u,Reels (a i) (X i))(hp:Whole K): Reels (e+loadᵣ a u) (junction p K X U u):= by
   induction u with
   | nil=> rw [junction]; exact Reels.none
   | cons i u ih=>
     have hu:=hx i List.mem_cons_self; have hk j hj:=hx j (List.mem_cons_of_mem (l:=u) i hj)
     rw [junction]; change Reels (e+(a i+loadᵣ a u)) (_+_)
     apply Reels.more _ _
     · rw [← add_assoc]; exact borne_r (thunder_r h hu hp) (cast_r hk)
     rw [add_left_comm]; exact borne_r hu (ih hk)
lemma zapH (h:∀ i∈u,Reels (a i) (X i))(hp:Whole K): Reels (loadᵣ a u) (pullG p K X u):= by
    induction u with
    | nil=> rw [pullG]; exact Reels.none
    | cons i u ih=>
      have ha:= h i List.mem_cons_self; have he j hj:= h j (List.mem_cons_of_mem (l:=u) _ hj)
      rw [pullG]; exact (junction_h (p:=p) ha he hp).more (borne_r ha (ih he))
private lemma glee_none (o:Site c): glee τ o (0:HeatS α)=0:= by funext i j; simp [glee,large]
lemma junctions (h:Reels e U)(hx:∀ i∈u, Reels (a i) (X i))(hp:Whole K)(z:Site c)(hh:(K.acts c)ᵀ=K.acts c):
    glee (e+loadᵣ a u) z (junction (some c) K X U u)= rim (K.acts c) (glee e z U) (glee (loadᵣ a u) z (castM X u)):= by
  induction u with
  | nil=>
    rw [junction,glee_none]; change (0:Op (Co c α))=rim (K.acts c) _ (glee 0 z (upstart α)); rw [glee_empty]
    suffices he: ∀ i:Co c α, sway (zpk i) (fun n j=> if n+j=0 then 1 else 0)=0 by rw [rimD]; simp only [he]; funext i j; simp [Finset.sum_apply,dancing]
    intro i; ext1 n; ext1 j; unfold sway; dsimp only; split <;> funext x <;> simp [Analysis.D]
  | cons i u ih=>
    have he j hj := hx j (List.mem_cons_of_mem (l:=u) _ hj); have hp':=hx i List.mem_cons_self; have hr:= cast_r he; have hA:= junction_h (e:=e) (p:=some c) h he hp
    let p:=loadᵣ a u; change glee (e+(a i+p)) z _= rim _ _ (glee (a i+p) z (borne (X i) (castM X u))); rw [junction]; rw [glee_m (show Reels _ _ from add_assoc e (a i) p ▸ borne_r (thunder_r (p:=some c) h hp' hp) hr) (show Reels _ _ from add_left_comm (a i) e p ▸ borne_r hp' hA), tempo_b hp' hr,duo_b _ (glee_sway hp' z) (glee_sway hr z) hh]; refine congr_arg₂ (·+·) ?_ ?_
    · rw [← add_assoc,tempo_b (thunder_r h hp' hp) hr,tempo_h h hp' hp]
    rw [add_left_comm e,tempo_b hp' hA,ih he]
lemma pulsed (hx:∀ i∈u,Reels (a i) (X i))(hp:Whole K)(z:Site c)(hh:(K.acts c)ᵀ=K.acts c)(S:Op (Co c α)) (hf:∀ i∈u,countT (glee (a i) z (X i))= coda (K.acts c) S (glee (a i) z (X i))) :
    let p:= glee (loadᵣ a u) z (castM X u)
    countT p=coda (K.acts c) S p-glee (loadᵣ a u) z (pullG (some c) K X u) := by
   dsimp only
   induction u with
   | nil=>
     change countT (glee 0 z (upstart α))=coda _ S (glee 0 z (upstart α))-glee 0 z (pullG _ _ X [])
     rw [pullG,glee_none,sub_zero,glee_empty]; funext i j x; simp only [countT,show ∀ k:ℕ,i+1+k≠0 from fun _=>by omega,↓reduceIte,smul_zero,coda,landP,rim,Pi.add_apply,Finset.sum_apply,Pi.zero_apply]
     have hz (n e:ℕ) x : lap (K.acts c) (if n+e=0 then 1 else 0) x = 0:= by split; exact congr_fun (lap_const (K.acts c) 1) x; exact congr_fun (lap_const (K.acts c) 0) x
     have hv (i':ℕ) (n:ℕ)(a:ℕ) (r:ℕ) x : arch (K.acts c) (if i'+n=0 then 1 else 0) (S a r) x=0:= by split <;> simp [arch,D]; -- specify Nat
     rw [hz]; simp_rw [hv]; simp
   | cons i u ih=>
     have he j hj:= hx j (List.mem_cons_of_mem (l:=u) _ hj); have hk:=hx i List.mem_cons_self; have hr:=cast_r he
     let p:= loadᵣ a u; let A:= pullG (some c) K X u
     change countT (glee (a i+loadᵣ a u) z (borne (X i) (castM X u)))=coda _ _ (glee (a i+loadᵣ a u) z (borne (X i) (castM X u)))-glee (a i+loadᵣ a u) z (pullG (some c) K X (i::u)) ; rw [tempo_b hk hr,pullG,glee_m (junction_h hk he hp) (borne_r hk (zapH he hp)),junctions hk he hp z hh,tempo_b hk (zapH he hp), countTn,hf i List.mem_cons_self, coda_wash hh (glee_sway hk z) (glee_sway hr z)]
     rw [ih he (fun j hj=> hf j (List.mem_cons_of_mem _ hj)),dsp]; abel
end spirit
end YM.RG08.Bands
