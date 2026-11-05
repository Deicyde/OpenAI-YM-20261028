import YM.MultipleContact.Center.March

/-! Anchor estimate on March profiles converted from Joins.Store by normalization. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.MultipleContact.Centered
open Filter Set Function MeasureTheory Extraction Spec Table Script Scene Drama ScheduleRow Bunching MergeProof RG
open scoped Classical Topology BigOperators


namespace March
variable {G:Gauge}{C:Family G}{L:Register G}
section
variable {S:Table L}
abbrev depth(p:March S) :=match p with | .field k=>k | .anchor k D=>k | .root k D=>k | .raw=>0
def toMode (p:March S):Mode :=match p with | .field _=>.fused | .raw => .raw | _=>.signed
end
variable {S:Table C.book}
def cue (p:March S): Detector S p.depth:=match p with | .raw=>Classical.choice (detector_exists _ _) | .field _ =>Classical.choice (detector_exists _ _) | .root k D => D | .anchor k D=>D
private def actual (p:March S)(q:p.Data):S.Field p.depth:=match p,q with | .field k,v=>v | .raw,_=>0 | .root ..,_=>0 | .anchor ..,_=>0
def takeOne (p:March S)(q:p.Data):S.Field p.depth:= (p.load q)⁻¹ • actual p q
lemma norm_takeOne (p:March S)(d:p.Data):‖takeOne p d‖≤ (1:ℝ):=by
   cases p with
   | raw=> simp [takeOne,actual]
   | anchor k D=>simp [takeOne,actual]
   | root k D=>simp [takeOne,actual]
   | field k=>
      have h0:0<((March.field k: March S).load d):=(.field k:March S)|>.load_pos _
      change ‖_ • (show S.Field k from d)‖≤1
      have h1: ‖(show S.Field k from d)‖≤ ((March.field k: March S).load d):= le_max_right ..
      rw [@norm_smul ℝ (S.Field k),Real.norm_eq_abs,abs_of_pos (inv_pos.mpr h0)]
      exact inv_mul_le_one_of_le₀ h1 h0.le -- check
lemma payload_one {n:ℕ}(H:S.Symmetric)(p:March S)(q:p.Data)(v:Fin n→S.Tag)(x:Fin n→E4)(s:E4):Indist S (p.payload v s x q) (((p.load q:ℝ):ℂ) • scaledBranch (d:=depth p) p.toMode v p.cue 1 s x (takeOne p q)):=by
       cases p with
       | raw=> simp only [payload,toMode,scaledBranch,load,Complex.ofReal_one,one_smul];intro; rfl
       | anchor k D=> simp only [cue,payload,residue,toMode,scaledBranch,load,Complex.ofReal_one,one_smul];intro; rfl
       | root k D=> simp only [cue,payload,residue,toMode,scaledBranch,load,Complex.ofReal_one,one_smul]; intro;rfl
       | field k=>
          simp only [payload,toMode,load,scaledBranch,takeOne]
          let v:= (show S.Field k from q); let u:=max 1 ‖v‖
          have hu :0 < u:= lt_max_of_lt_left zero_lt_one
          let y:=((u:ℝ)⁻¹ • v)
          suffices he:Indist S (insertion S s v) ((u:ℂ) • insertion S s y) from he
          have heq:v=(u:ℝ) • y := by unfold y;rw [smul_smul,mul_inv_cancel₀ hu.ne',one_smul]
          intro f; nth_rw 1 [heq]; rw [insertion,show (u:ℝ) • y=(u:ℂ) • y from rfl, inline_smul S H s f _ _,smul_mul_assoc,map_smul]; rfl
lemma trigger_step {n:ℕ}[Inhabited (Fin n)](g:March S)(N:Lattice.Side)(r:ℝ)(x:Fin n→E4)(hr:0<r)(hv:g.allow N r x)(hm:g.toMode≠.fused)(h:∀ k D,g≠March.root k D):
      let o:=if g.toMode=.raw then x default else 0
      Cord.Near n (Joins.expand N 2) r (x-fun _=>o):=by
       intro o
       have hub: (1:ℝ) ≤ (N.val:ℝ) := by exact_mod_cast N.pos
       have hvb: (N.val:ℝ)*r>0:=mul_pos (zero_lt_one.trans_le hub) hr
       cases g with
       | root k D=> exact (h _ _ rfl).elim
       | raw=> refine ⟨?_,fun i j h=>by dsimp only [March.toMode,if_true,Pi.sub_apply]; simpa only [sub_sub_sub_cancel_right] using hv.1 i j h,?_⟩
               swap
               · change ∀s,‖x s-x default‖ < (2* ((N.val*(2+1):ℕ):ℝ)*r)
                 intro s; push_cast
                 linarith only [hv.2.1 s,hv.2.1 default, norm_sub_le (x s) (x default),hvb]
               exact sub_self _
       | anchor k D=> have ho:o=0:=rfl; rw [ho,show (fun _:Fin n=> (0:E4))=0 from rfl,sub_zero]
                      have he:x default=0:= hv.2.2 _ _ rfl
                      refine ⟨he,hv.1,fun s=>?_⟩
                      change ‖x s‖ < (2* ((N.val*(2+1):ℕ):ℝ)*r); push_cast; linarith only [hv.2.1 s,hvb]
       | field k=> exact (hm rfl).elim
lemma weight_same {b:ℕ}{n:Fin b→ℕ}(p:Fin b→March S)(V:∀i,Fin (n i)→S.Tag)(ε:ℝ)(i:Fin b): (p i).weight (V i) ε = Joins.weight (d:=fun i=>depth (p i)) (p · |>.toMode) V (p · |>.cue) ε i:=by unfold Joins.weight;cases h:(p i) with
        | raw=> simp [weight,depth,toMode,h]
        | field k=> simp [weight,depth,toMode,h]
        | anchor k D=> simp [weight,depth,toMode,h]
        | root k D=>simp [weight,depth,toMode,h]
lemma credit_near {b:ℕ}{n:Fin b→ℕ}(p:Fin b→March S)(q:∀i,(p i).Data)(ε:ℝ)(V:∀i,Fin (n i)→S.Tag)(ρ:Fin b→ℝ):Joins.due (d:=fun i=>depth (p i)) V (p ·|>.cue) (p · |>.toMode) ρ ε * ∏ i:Fin b,(p i).load (q i) = plainLoad p V ε ρ q:=by
          unfold plainLoad March.credit; rw [Finset.prod_mul_distrib];congr 1
          exact Finset.prod_congr rfl fun i _=>by rw [weight_same p V ε i]
end March
open March
lemma close_shift {b:ℕ}{z e:Fin b→ E4}{κ:ℝ}(hc:Joins.Close z κ)(hp:0<κ)(h:∀i,‖e i‖ < κ/4):Joins.Close (z+e) (κ/2):= by
        intro i j hij
        have hz (i): ‖z i-(z+e) i‖=‖e i‖:=by simp [Pi.add_apply]
        linarith only [hc i j hij, norm_sub_le_norm_sub_add_norm_sub (z i) ((z+e) i) (z j), -- bad application replace
                        norm_sub_le_norm_sub_add_norm_sub ((z+e) i) ((z+e) j) (z j), norm_sub_rev ((z+e) j) (z j),h i,h j,hz i,hz j]
lemma voucher0 {G:Gauge}{C:Family G}{S:Table C.book}(H:S.Symmetric)(hs:∀k,Joins.Store S k):Good 0 S:=by
        intro b n _ p V ε κ N hε hp hc
        have hL(i:Fin b):∀k D,p i≠ March.root k D:=by
             intro k D he; have : amount p ≠ 0:= Finset.card_ne_zero_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [he];rfl⟩) -- implicit type? specify
             omega
        obtain ⟨K,r,Hk,Hr,hstore⟩:= hs b b n V _ (p ·|>.cue) (p ·|>.toMode) (Finset.card_filter_le _ _|>.trans_eq (Finset.card_univ.trans (Fintype.card_fin ..))) (κ/2) ε (half_pos hp) hε (Joins.expand N 2) -- b repeated ok
        let t:=min r (κ/(9*(N.val:ℝ)))
        have hN:0<(N.val:ℝ):=by exact_mod_cast N.pos
        refine ⟨K,Hk,t,lt_min Hr (by positivity : 0<κ/(9*(N.val:ℝ))),?_⟩
        intro q ρ z x ht
        let e(i):=if (p i).toMode=.raw then x i default else 0
        let x'(i)(s:Fin (n i)):= x i s-e i
        have he(i):‖e i‖<κ/4 := by
            unfold e; split
            · rename_i he
              have h0:‖x i default‖< 2*N.val*ρ i:= by
                have hh:p i=.raw:=by cases hv:(p i) <;> simpa [hv,March.toMode] using he
                have hh:= hh ▸ ht.2.2 i; exact hh.2.1 default
              have hK:(ρ i)*(9*N.val)<κ:=lt_div_iff₀ (by positivity) |>.1 ((ht.2.1 i).2.trans_le (min_le_right ..)) -- parser
              linarith only [hK,h0,mul_pos hN (ht.2.1 i).1]
            simp only [norm_zero]; positivity
        have hh:= hstore (z+e) (close_shift ht.1 hp he) ρ (fun i=>⟨(ht.2.1 i).1,(ht.2.1 i).2.trans_le (min_le_left ..)⟩) x' (fun i hi=> March.trigger_step (p i) N (ρ i) _ (ht.2.1 i).1 (ht.2.2 i) hi (hL i)) (fun i=>takeOne _ (q i)) (fun i h=>norm_takeOne _ _)
        let F(i):= scaledBranch (S:=S) (d:=(p i).depth) (p i |>.toMode) (V i) (p i|>.cue) 1 ((z+e) i) (x' i) (takeOne _ (q i))
        let A:Grammar (Alpha S):= ∏ i:Fin b,((load (p i) (q i):ℝ):ℂ) • F i
        have hZ'(i):F i = scaledBranch (S:=S) (d:=(p i).depth) ((p i).toMode) (V i) ((p i).cue) 1 (z i) (x i) (takeOne (p i) (q i)):=by
           unfold F; by_cases hb:(p i).toMode=.raw
           · unfold scaledBranch; rw [hb]
             dsimp only [Scene.packet,Pi.add_apply,x']
             have h':∀j,z i+e i+(x i j-e i)=z i+x i j:=fun j=> by abel
             simp_rw [h']
           simp [e,hb,x']
        have hZ(i): Indist S ((p i).payload (V i) (z i) (x i) (q i)) (((p i).load (q i):ℂ) • F i):=by rw [hZ']; exact payload_one H _ _ _ _ _
        have hX: Indist S (work p V z x q) A:= prod_indist S (fun i _=>hZ i) -- implicit arguments
        rw [reading_eq S hX]
        unfold A; rw [Finset.prod_smul,map_smul,norm_smul,← Complex.ofReal_prod,Complex.norm_real,Real.norm_of_nonneg (Finset.prod_nonneg (fun i _=>(load_pos ..).le)),← credit_near]
        exact (mul_le_mul_of_nonneg_left hh (Finset.prod_nonneg (fun i _=> (load_pos ..).le))).trans_eq (by ring)
end YM.MultipleContact.Centered
