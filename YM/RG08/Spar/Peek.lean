import YM.RG08.Spar.Clean
import YM.RG08.Isles.Accord

noncomputable section
namespace YM.RG08.Spar
open Forms Rudder Packets Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch Anchor Symmetry Isles Stationary RG Rows
open scoped Topology BigOperators Classical ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I J : Type}{n:ℕ}{c L:Side}{θ C τ:ℝ}

def cardMat (K:Kernel I J)(c:Side): Matrix (Co c I) (Co c J) ℝ:=Matrix.of (fun x y=>display K c (reach x) y)
lemma cardDeck {K:Kernel I J}[Fintype J](h:Priced θ C K):Tagged θ C K (cardMat K):=by
 refine ⟨h,fun n ⟨x,i⟩ y=>?_⟩
 simp_rw [cardMat,Matrix.of_apply,circuit]
 let t :=Stationary.rent n x
 let E:=Equiv.addRight t
 rw [← E.tsum_eq (fun w=>K (x,i) (Lattice.lift y.1+n.val • w,y.2))]
 apply tsum_congr;intro w
 have he:=h.city (Lattice.lift (wrap n x),i) (Lattice.lift y.1+n.val•w,y.2) (n.val•t)
 rw [show (1:Side).val=1 from rfl,one_smul] at he
 apply Eq.trans _ he
 dsimp [pass,E,reach]
 rw [← rent_balance, smul_add];congr 2;abel

-- finite multilinear all-leg transmission, defined on any finite sets; including ranks with
-- both zero and nonzero costs.
def query {A B:Type}[Fintype A](T:A→B→ℝ)(F:Flake n A):Flake n B:= fun x=>∑ y,F y * ∏ j,T (y j) (x j)
lemma query_rafts {A B:Type}[Fintype A](T:A→B→ℝ)(F:Flake n A):query T F=raft (fun _=>T) F:=by ext; simp only [query,raft,vat,tsum_fintype,design]

lemma braces_farm (K:Kernel I J)(F:Flake n (Market I)) : braces (clover L K) (farm L F)=braces K F:=by
 funext y; unfold braces raft vat;exact Equiv.tsum_eq (carton n _ _ (Cell.column L I)) (fun w:Tape n (Market I)=>vat (fun _=>K) F y w)
/- This was not a well-formed theorem statement and has no elaborated predecessor.
lemma sizeEyes {s:ℕ→Side}{f:(m:ℕ)→Flake n (Cove (s m) I)}{F:Flake n (Market I)}(G:ViewDeck n I)(hg:Eyes G F)
   (h:tendstoNat s)(he:∀ m x:Tape n (Market I),f ?m..):True:=trivial -- remove template -/

variable [Fintype I][Fintype J]
/- Its matrix has an unpacked fine-site index,
while clover uses a packed-cell index.
lemma prices_seen {K:Kernel I J}{l:ℕ→Side}(ht:Tendsto (fun m=>(l m).val) atTop atTop){S:(m:ℕ)→StepData (l m) ((l m)*L)}(hl:∀ m,(S m).ratio.count=L)
 {A:(m:ℕ)→Matrix (Co (l m*L) I) (Co (l m) J) ℝ}(hk:∀ m,Matches (clover L K) ((fun x y=>A m x y))) := True.intro -- actually need repack with cast count; avoid S -/

lemma suppliesSeen {K:Kernel I J}{l:ℕ→Side}(ht:Tendsto (fun m=>(l m).val) atTop atTop){M:(m:ℕ)→Matrix (Co (l m) I) (Co (l m) J) ℝ}
    {F:Flake n (Market I)}(i:Fin n)(hv:0<θ)(hC:Priced θ C K)(hr:0≤τ)(h:Cohort F)(hp: Held (carpet I) θ τ F)(hM:∀ m,Matches K (M m))(x:Tape n (Market J)):
    Tendsto (fun m=>query (fun a b=>M m a b) (pour F i) (port (l m) ∘ x)) atTop (𝓝 (braces K F x)):=by
 -- use cofinal by composing previously checked positive-width Studies
 let N m:ℕ:=(l m).val-1
 have he(m):chain (N m)=l m:=Subtype.ext (by have hz:0<(l m).val:=(l m).pos;change (l m).val-1+1=(l m).val;omega)
 have hn:Tendsto N atTop atTop:=tendsto_atTop.mpr fun b=> (ht.eventually (eventually_ge_atTop (b+1))).mono fun m hm=>by unfold N;change b+1≤(l m).val at hm;omega
 let B:=(Fintype.card I+Fintype.card J:ℝ)*C
 have hs:=Isles.tagged (cardDeck hC) hv
 have hw:= ((Isles.bureau h hp hv hr i).morph (q:=fun _=> B) (fun _:Fin n=>hs)).light (Fin.pos i) x
 have hA(m)(a:Cove (l m) I)(b:Cove (l m) J):M m a b=cardMat K (l m) a b:=by
   apply Eq.trans (b:=display K (l m) (reach a) b)
   · rw [(hM m)];simp [reach]
   rfl
 refine (hw.comp hn).congr' (Eventually.of_forall (fun m=> ?_))
 dsimp only [comp_apply]
 change raft (fun _ a b=>cardMat K (chain (N m)) a b) (pour F i) (port (chain (N m)) ∘ x)=_
 simp_rw [hA];rw [query_rafts];apply congr_arg (fun c:Side=>raft (fun _ a b=>cardMat K c a b) (pour F i) (port c ∘ x)) (he m)
end YM.RG08.Spar
