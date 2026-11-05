import YM.MultipleContact.Multi.Letting
import YM.MultipleContact.Multi.Branch
import YM.MultipleContact.Multi.Terrain
import YM.MultipleContact.Multi.Speck


set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace YM.MultipleContact.Drama
open Function Filter MeasureTheory Lattice Wilson RG Extraction Table Spec Cells Script Ward Set BigOperators
open Flight Scene
open scoped Topology BigOperators InnerProductSpace ContDiff Classical
inductive Mode | signed | raw | fused deriving Fintype,DecidableEq
variable {I:Type*}{L':Type*}[Fintype I][DecidableEq I]
variable {G:Gauge} {L:Register G}{C:Family G}{S:Table L}
-- slot counts include raw leaves, actual subtraction anchor independent.
abbrev Symbols (n:I→ℕ):= Sigma (fun i=> Option (Fin (n i)))
-- omit
def leaf {n:I→ℕ} (i:I)(s:Fin (n i)): Symbols n:=⟨i,some s⟩
def hub (n:I→ℕ)(i:I):Symbols n:=⟨i,none⟩
def text (n:I→ℕ) (w:ℝ)(g:Mode)(i:I):Grammar (Symbols n) :=match g with
   | Mode.signed=> (w:ℂ) • spell (leaf i) - stamp (hub n i)
   | .raw=>spell (leaf i)
   | .fused=>stamp (hub n i)
def token {n:I→ℕ}{d:I→ℕ} (v:∀i,Fin (n i)→S.Tag)(u:∀i,S.Field (d i))(x:Symbols n):S.Tag:= match x with | ⟨i,none⟩=>⟨_,u i⟩ | ⟨i,some k⟩=>v i k
lemma token_leaf {n:I→ℕ}{d:I→ℕ}(v:∀i,Fin (n i)→S.Tag)(u:∀i,S.Field (d i))(j)(s:Fin (n j)): token v u (leaf j s)=v j s:=rfl
lemma token_hub {n:I→ℕ}{d:I→ℕ}(v:∀i,Fin (n i)→S.Tag)(u:∀i,S.Field (d i))(j): token v u (hub n j)=⟨d j,u j⟩:=rfl
variable {n d:I→ℕ}
def site (z:I→ E4)(x:∀i,Fin (n i)→ E4)(y:Symbols n):E4:= match y with | ⟨i,none⟩=>z i | ⟨i,some s⟩=>x i s+z i
def expression (g:Mode)(w:ℝ){m k:ℕ}(v:Fin m→S.Tag)(u:S.Field k) (z:E4)(y:Fin m→ E4):=match g with | Mode.signed=> (w:ℂ) • packet S v y z- insertion S z u | .raw=>packet S v y z | .fused=>insertion S z u
lemma step (w:ℝ)(g:Mode)(v:∀i,Fin (n i)→S.Tag)(u:∀i,S.Field (d i))(z:I→ E4)(y:∀i,Fin (n i)→ E4)(j:I):
   Script.rewrite (fun i:Symbols n=>(token v u i,site z y i)) (text n w g j) = expression g w (v j) (u j) (z j) (y j):=by
       cases g <;> simp only [text,expression,map_smul,map_sub,rewrite_stamp,rewrite_spell,leaf,hub,packet,call,insertion,token,site,Function.comp_def,add_comm]

-- cutoff reading for arbitrary snapshot.
def loc (z:I→ Cover) (y:∀i,Fin (n i)→ Cover)(x:Symbols n):Cover:=match x with | ⟨i,none⟩=> z i | ⟨i,some s⟩=>y i s + z i
lemma site_loc (z:I→ Cover) (y:∀i,Fin (n i)→ Cover)(t:ℕ)(S:Schedule): site (S.gridPoint t∘z) (fun i=>S.gridPoint t∘y i)=S.gridPoint t ∘ loc z y:=by
       funext i; rcases i with ⟨i, _|i⟩
       · ext a; simp [site,loc]
       ext a; simp [site,loc,Schedule.gridPoint,mul_add]
def prot (v:∀i,Fin (n i)→ C.book.Token)(u:∀i,C.book.Ref (d i))(x:Symbols n):C.book.Token:=match x with |⟨i,none⟩=>⟨_,u i⟩ | ⟨i,some s⟩=>v i s
def wordLeaf (v:∀i,Fin (n i)→ C.book.Token)(u:∀i, C.book.Ref (d i))(P:Table C.book)(x:Symbols n): P.Tag := token (fun i s=>(P.classTokens (v i s))) (fun i=>(P.project (d i) (u i))) x
lemma word_eq (v:∀i,Fin (n i)→ C.book.Token)(u:∀i,C.book.Ref (d i))(P:Table C.book)(x:Symbols n): wordLeaf v u P x = P.classTokens (prot (C:=C) v u x):= by rcases x with ⟨i,s⟩;cases s <;> rfl
variable (w:I→ℝ)(v:∀i,Fin (n i)→ C.book.Token)(u:ℕ×ℕ→∀i,C.book.Ref (d i))
private abbrev Cfg (C:Family G)(k:ℕ×ℕ):=Config G (C.side k.1 k.2)
def Farm (C:Family G) := ∀k:ℕ×ℕ,Cfg C k→ℂ
def Loss (C:Family G){n d j:ℕ}(x:Fin n→ Cover)(V:Fin n→ C.book.Token)(w:ℝ)(u:ℕ×ℕ→ C.book.Ref d):Farm C:= fun k W=> (w:ℂ)*(∏s:Fin n,C.seen (V s) (location C.S j k.1 k.2 (x s)) W)-C.O k.1 k.2 (d:=d) (u k) 0 W
def Unit (C:Family G){d:ℕ}(u:C.book.Ref d) : Farm C:= fun k=>C.O k.1 k.2 (d:=d) u 0
def Fused (C:Family G){d:ℕ}(u:ℕ×ℕ→ C.book.Ref d): Farm C:= fun k=>Unit C (d:=d) (u k) k
def Wage (F:Extraction.Order)(C:Family G)(f:Farm C)(J:ℕ)(A:ℝ):Prop:=∀ᶠ i in F.fuse,∃ (h:J ≤ i.1),let T:=Cells.center C.S i.2 h 0; Interior (T.chamber 0) (f i) ∧ T.rootTest (C.beta i.1 i.2) (f i) ≤ A

def trial (x:∀i,Fin (n i)→ Cover)(t:ℕ)(g:Mode)(p:I) : Farm C:= match g with | Mode.signed=>Loss C (j:=t) (x p) (v p) (w p) (fun i=> u i p) | .raw=>fun i W=>∏s,C.seen (v p s) (location C.S t i.1 i.2 (x p s)) W | .fused=>fun i=>C.O i.1 i.2 (d:=d p) (u i p) 0
private lemma location_add (S:Schedule)(t:ℕ)(i:ℕ×ℕ)(x y:Cover): location S t i.1 i.2 (x+y)=location S t i.1 i.2 x+location S t i.1 i.2 y:= by
    unfold location; split
    · rw [map_add,←Ratio.root_embed,map_add,Ratio.root_embed,Ratio.root_embed]
    exact (add_zero (0:_)).symm
lemma report_form (z:I→ Cover) (y:∀i,Fin (n i)→ Cover)(t:ℕ)(g:I→Mode)(k:ℕ×ℕ):
   report C (∏ i:I,text n (w i) (g i) i) (loc z y) t (prot v (u k)) k = moment (C.beta k.1 k.2) (fun f:Cfg C k=>∏i:I, (trial w v u y t (g i) i k) (translate (Cells.location C.S t k.1 k.2 (z i)) f)):=by
      let r:=loc z y; unfold report; congr 1
      funext f; rw [map_prod]
      refine Finset.prod_congr rfl fun i _=>?_ ; let l:=location C.S t k.1 k.2; let f':= (translate (l (z i)) f)
      have hx:C.seen (prot v (u k) (hub n i)) (l (r (hub n i))) f=C.O k.1 k.2 (u k i) 0 f':=by rw [C.translation,zero_add];rfl
      have hq : (∏s:Fin (n i), C.seen (prot v (u k) (leaf i s)) (l (r (leaf i s))) f)=∏ s,C.seen (v i s) (l (y i s)) f':=Finset.prod_congr rfl fun s _=> by
         change C.O k.1 k.2 (d:=(v i s).1) (v i s).2 (l (y i s+z i)) f = _; unfold f' Family.seen; rw [C.translation, show l = Cells.location _ _ _ _ from rfl, location_add C.S t k]
      cases h:g i <;> simp only [text,map_sub,map_smul,assign_spell,trial]
      · unfold assign stamp; simp only [AddMonoidAlgebra.lift_single, one_smul] -- actual names replace
        change (↑(w i):ℂ)*(∏ s:Fin (n i),_) - ((({hub n i}:Multiset (Symbols n)).map _).prod:ℂ)=_; simp only [Multiset.map_singleton,Multiset.prod_singleton]; exact congr_arg₂ (fun p q:ℂ=>(w i:ℂ)*p-q) hq hx
      · exact hq
      unfold assign stamp; rw [AddMonoidAlgebra.lift_single,one_smul]; change (Multiset.map (fun p=>C.seen (prot v (u k) p) (location C.S t k.1 k.2 (loc z y p)) f) ({hub n i}:Multiset (Symbols n))).prod=_; simp only [Multiset.map_singleton,Multiset.prod_singleton]; exact hx

def far (a:ℝ)(z:I→ E4):=∀i j:I,i≠j→ 4*a<‖z i-z j‖
lemma disj_sites {ι:Type*}{t:ℝ}{z:ι→ E4}{K:ι→ Set E4}(ht:far t z)(hK:∀i,∀ w∈K i, ‖w-z i‖≤t):∀ i j:ι,i≠j→ Disjoint (K i) (K j):=by
      intro i j he; rw [Set.disjoint_left]; intro a h h'
      have h:=hK i _ h; have h':=hK j _ h'
      linarith only [norm_sub_le_norm_sub_add_norm_sub (z i) a (z j), ht _ _ he, h,h', norm_nonneg (a-z i), norm_sub_rev (z i) a]
-- Characterize axis-admissible words over disjoint name margins. No omission of mixed terms.
-- include
lemma allowed_full {W:Type*}{Z:Symbols n→W}{K:I→Set W}(hd:∀i i':I,i≠i'→ Disjoint (K i) (K i')) (w:I→ℝ)(g:I→Mode)(h:∀i,∀j:Option (Fin (n i)), Z (Sigma.mk i j)∈ K i)(hP:∀ i,g i≠ Mode.fused→ Injective (fun j:Fin (n i)=>Z (leaf i j))): Admissible Z univ (∏i,text n (w i) (g i) i):=by
       refine Admissible.weak (Set.subset_univ _) (admissible_prod (P':=K) (Q:=(Finset.univ:Finset I)) ?_ (fun r _ s _ he=>hd r s he))
       intro i hi
       have hT:Admissible Z (K i) (stamp (hub n i)):=by
           rw [show stamp (hub n i) = spell (fun (_:Fin 1)=>hub n i) from (by simp [spell])]; exact admissible_spell _ (fun i j h=> Subsingleton.elim ..) (fun j=>h i none)
       have hU : g i ≠Mode.fused → Admissible Z (K i) (spell (leaf (n:=n) i)):=fun hi=> admissible_spell _ (hP i hi) (fun s=>h i (some s))
       cases e:(g i)
       · exact (hU (by simp [e])).scalar ((w i:ℝ):ℂ) |>.diff hT
       · exact hU (by simp [e])
       exact hT
open Flight
lemma coordinates (x:∀ i,Fin (n i) → E4)(z:I → E4)(l:I→ℕ)(g:I→Mode)
    (r:∀i,Fin (n i)→ Cover)(hR:∀i,g i=Mode.signed→ x i=C.S.gridPoint (l i)∘r i)(hsigned:∀i,g i=Mode.signed→∀a:Axis,Injective ((fun y:E4=>y a) ∘ x i)):
    ∃ (z₀:ℕ→I→ Cover)(x₀: ℕ→∀i,Fin (n i)→ Cover), let zi(t i):= C.S.gridPoint t (z₀ t i); let xi(t i):= C.S.gridPoint t ∘ x₀ t i; (∀i,Tendsto (zi · i) atTop (𝓝 (z i))) ∧(∀i,Tendsto (xi · i) atTop (𝓝 (x i)))∧∀ᶠ t in atTop,(∀a:Axis,∃K:I→Set ℝ, (∀q:Symbols n,(site (zi t) (xi t) q a)∈K q.1)∧(∀i i':I,i≠i'→Disjoint (K i) (K i')))∧ (∀i,∀a:Axis,Injective fun (s:Fin (n i))=>site (zi t) (xi t) (leaf i s) a)∧ ((∀i,g i=Mode.signed→ ∃h:l i ≤ t, x₀ t i=fun j=> YM.Next.UVStress.pushSite C.S h (r i j))) := by
       let base:=site z x; let off(q:Symbols n):= (match q with | ⟨i,some _⟩=>({0}:Finset E4) | ⟨i,none⟩=> if g i = Mode.signed then insert 0 ((Finset.univ).image (x i)) else {0})
       obtain ⟨f,hf,hSEP⟩:=speck base off C.S
       let better(t i) : Fin (n i)→ Cover:=if h: l i ≤ t then (Next.UVStress.pushSite C.S h ∘ (r i)) else 0
       let grab (t i s):Cover:=if g i=Mode.signed then better t i s else f t (leaf i s)-f t (hub n i)
       have eventually_t:∀ᶠ t in (atTop:Filter ℕ),∀i:I,l i ≤ t:=eventually_all.mpr fun i=>eventually_ge_atTop _
       let first t i:= f t (hub n i); let z'(t i):=(C.S.gridPoint t ∘ first t) i; let y'(t i s):= C.S.gridPoint t (grab t i s)
       have hp i := hf (hub n i); change ∀ i,Tendsto (z' · i) atTop (𝓝 (z i)) at hp
       have he(t i)(h:l i≤t)(j:Fin (n i))(hs:g i=Mode.signed):y' t i j=x i j:=by
              unfold y' grab; rw [if_pos hs]; unfold better; rw [dif_pos h,hR i hs];exact YM.Next.UVStress.finer ..
       have hr(t i) (j:Fin (n i))(h:g i≠ Mode.signed):y' t i j+z' t i = C.S.gridPoint t (f t (leaf i j)):=by
              unfold y' grab z' first; rw [if_neg h]; dsimp only [Function.comp_apply]; ext a
              change C.S.a t*((f t (leaf i j) a - f t (hub n i) a:ℤ):ℝ) + C.S.a t*↑(f t (hub n i) a) = C.S.a t*↑(f t _ a); push_cast; ring
       refine ⟨first,grab,hp,fun i=>?_ ,?_⟩
       · by_cases h:g i=Mode.signed
         · exact tendsto_pi_nhds.mpr fun j=> by
             refine tendsto_const_nhds.congr' ?_
             filter_upwards [eventually_t] with t ht
             exact (he t i (ht i) j h).symm
         apply tendsto_pi_nhds.mpr fun j=> ?_
         have hd:= (hf (leaf i j)).sub (hf (hub n i)); change Tendsto _ _ (𝓝 ((x i j+z i)- z i)) at hd; rw [add_sub_cancel_right] at hd
         exact hd.congr fun t=> (eq_sub_of_add_eq (hr t i j h)).symm
       filter_upwards [eventually_t] with t ht
       have pick(i)(s:Option (Fin (n i))):∃q:Symbols n,q.1=i∧∃ v∈off q, C.S.gridPoint t (f t q)+v=site (z' t) (y' t) (Sigma.mk _ s):=by
           have zero_on : (0:E4)∈off (hub n i):=by unfold off hub; dsimp only; split <;> simp
           rcases s with _|s
           · exact ⟨hub n i,rfl,0,zero_on,add_zero _⟩
           by_cases h:g i=Mode.signed
           · exact ⟨hub n i,rfl,x i s,by change (x i s∈if _ then insert 0 ((Finset.univ).image (x i)) else _); rw [if_pos h]; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)),by change z' t i+_ = y' t i s+z' t i; rw [he _ _ (ht i) _ h]; rw [add_comm]⟩
           exact ⟨leaf i s,rfl,0,Finset.mem_singleton_self _,by rw [add_zero]; exact (hr t i s h).symm⟩
       let K(a:Axis)(i:I):Set ℝ:=Set.range (fun (s:Option (Fin (n i)))=>site (z' t) (y' t) (Sigma.mk i s) a)
       have hS:=hSEP t
       refine ⟨fun a=>⟨K a,fun q=> ?_, fun i i' he=>?_⟩, ?_,?_⟩
       · rcases q with ⟨x,y⟩; exact ⟨y,rfl⟩
       · rw [Set.disjoint_left];rintro s ⟨j,hj⟩ ⟨k,hk⟩; obtain ⟨t',ht',b,hb,h⟩:=pick i j
         obtain ⟨v',hv',c,hc,e⟩:=pick i' k
         exact (hS t' v' (by intro eq; apply he; exact ht'.symm.trans ((congr_arg Sigma.fst eq).trans hv')) b hb c hc a (by change (C.S.gridPoint t (f t t')+b) a = (C.S.gridPoint t (f t v')+c) a; rw [h,e]; exact hj.trans hk.symm))
       · intro i a j j' h
         change y' t i j a+z' t i a=y' t i j' a+z' t i a at h
         by_cases he':g i=Mode.signed
         · rw [he t i (ht i) j he',he t i (ht i) j' he'] at h
           exact hsigned i he' a (add_right_cancel h)
         by_contra ne
         have hleaf: leaf (n:=n) i j ≠ leaf i j':=by simpa [leaf] -- HEq
         exact hS _ _ hleaf _ (show (0:E4)∈off (leaf i j) from (by change (0:E4)∈ ({0}:Finset E4); simp)) _ (show (0:E4)∈off (leaf i j') from (by change (0:E4)∈ ({0}:Finset E4);simp)) a ( by dsimp only [comp_apply,PiLp.zero_apply]; rw [← hr t i j he',← hr t i j' he',add_zero,add_zero];exact h)
       exact fun i he=> ⟨ht i,funext fun s=> by unfold grab; rw [if_pos he]; unfold better; rw [dif_pos (ht i)];rfl⟩
end YM.MultipleContact.Drama
