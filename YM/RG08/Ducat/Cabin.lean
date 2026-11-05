import YM.RG08.Ducat.Town
import YM.RG08.Steam.Ballot
/-! # Single aperture bills on incidence alphabet Foil. !-/
noncomputable section
namespace YM.RG08.Ducat
open Filter Function Lattice Laurent Pert.Bulk Forms Room Steam Isles Rows Gauge Finset
open scoped Classical BigOperators PowerSeries Topology
set_option autoImplicit false
variable {O:Type} {I J : O→Type}{n:ℕ}{w d:O→ℝ}(D:Exchange O)

/-- geometry receipts at shared cell widths. caller supplies these changing precision and any
 involved Gram constants in same post budget, period-independent. -/
def Orbit (I J:O→Type)(w d:O→ℝ)(p q:∀ i:O,Kernel (I i) (J i)):=∃ a,D.Good a ∧ ∀ i,Priced (w i) (a i) (p i) ∧ Priced (w i) (a i) (q i) ∧ Priced (w i) (a i*d i) (p i-q i)
variable {D} [∀ i,Fintype (I i)][∀ i,Fintype (J i)]
def Counter (I J:O→Type) [∀ i,Fintype (I i)][∀ i,Fintype (J i)] (w d:O→ℝ)(p q:∀ i:O,Kernel (I i) (J i)):Prop := Orbit D I J w d p q ∧ D.Good fun j=> Fintype.card (I j)+Fintype.card (J j)
variable {p q:∀ i:O,Kernel (I i) (J i)}{G T:∀ i:O,Kernel (I i) (I i)}
lemma counts (h:Counter (D:=D) I I w d G T)(he:∀ i,0<w i):∃ a,D.Good a ∧ ∀ i, WireCot (carpet _) (w i) (d i) (a i) (G i) (T i):=by
 obtain ⟨⟨a,ha,hp⟩,ht⟩:=h
 refine ⟨_,D.moreover _ _ ht ha,fun i=>?_⟩
 have h {K :Kernel (I i) (I i)}{x:ℝ}(hk:Priced (w i) x K):Wire (carpet _) (w i) (((Fintype.card (I i)+Fintype.card (I i):ℝ)*x)) K:= (Isles.tagged (Spar.cardDeck hk) (he i)).line.palm
 exact ⟨h (hp i).1,h (hp i).2.1, (mul_assoc (Fintype.card (I i)+Fintype.card (I i):ℝ) (a i) (d i)).symm ▸ h (hp i).2.2⟩

def lamp (i:O)(w:ℝ): Cables n (Market (I i)) (Market (J i)):= fun _ a b=>w*sep a.1 b.1
lemma censorship (h:Counter (D:=D) I J w d p q)(he:∀ i,0<w i)(n:ℕ): ∃ a,D.Good a ∧ ∀ i, Alley (carpet _) (carpet _) (w i) (w i) (d i) (a i) (lamp i (w i)) (repeatLine (p i) n) (repeatLine (q i) n):=by
 obtain ⟨⟨a,ha,hp⟩,ht⟩:=h
 refine ⟨_,D.moreover _ _ ht ha,fun x=>?_⟩
 let t:ℝ:= (Fintype.card (I x)+ Fintype.card (J x):ℝ)
 have hg {K:Kernel (I x) (J x)}{z:ℝ}(hK:Priced (w x) z K):Forms.street (lamp x (w x)) (repeatLine K n) (fun _=> t*z):=by
   have hv:=Isles.tagged (Spar.cardDeck hK) (he x)
   exact fun _=>⟨hv.cost,hv.near,hv.far⟩
 have he':0 ≤ w x:= (he x).le
 refine ⟨mul_nonneg (show 0 ≤ t from D.safe _ ht x) (D.safe _ ha x),hg (hp x).1,hg (hp x).2.1,?_,fun V _=> ⟨he',he',fun _ _ _ => mul_nonneg he' (sep_nonneg ..),fun _ _ _ i j r s _ _=>?_⟩⟩
 · exact (mul_assoc t (a x) (d x)).symm ▸ hg (hp x).2.2
 change w x*sep _ _ ≤ w x*sep _ _+w x * sep _ _+w x*sep _ _
 exact (mul_le_mul_of_nonneg_left (calc
    sep r.1 s.1 ≤ sep i.1 r.1+sep i.1 s.1:=by simpa only [sep_comm r.1 i.1] using! sep_triangle r.1 i.1 s.1
    _ ≤ sep i.1 j.1+sep i.1 r.1+sep j.1 s.1:=by linarith only [sep_triangle i.1 j.1 s.1]) he').trans_eq (by ring)

variable (he:∀ i,0<w i)(hd:∀ i,0 ≤ d i)
 include he hd
-- collision n declaration above
lemma Lance.reserve {n:ℕ}{V A:(x:O)→Flake n (Market (I x))}(H:Lance D w d V A)(h:Counter (D:=D) I J w d p q): Lance D w d (fun x=>Forms.raft (repeatLine (p x) _) (V x)) (fun x=>Forms.raft (repeatLine (q x) _) (A x)):=by
 obtain ⟨a,ha,h⟩:=censorship h he n
 obtain ⟨b,hb,H⟩:=H
 exact ⟨_,D.moreover _ _ (D.moreover _ _ (D.steady (((n:ℝ)+1)) (by positivity)) hb) (stairs D ha n),fun i=>(H i).raft (h i) (hd i)⟩

lemma receipt_step (hι:Counter (D:=D) I J w d p q) (hΓ:Counter (D:=D) I I w d G T) (V A:∀ i,Steam.Grain (Market (I i)))(hV:∀ i,Steam.Eligible (V i))(hA:∀ i,Steam.Eligible (A i))(e n:ℕ)
   (hc:∀ a r,Steam.Residual e n a r→ Lance D w d (fun i=>V i a r) fun i=> A i a r)(hn:0<n): Lance D w d (fun i=> Steam.strict (G i) (V i) (p i) e n) (fun i=>Steam.strict (T i) (A i) (q i) e n):=by
 obtain ⟨b,hb,HP⟩:=Steam.paving e n hn
 obtain ⟨c,hB,h⟩:= censorship hι he n
 obtain ⟨γ,hγ,hT⟩:= counts hΓ he
 -- max local powers, assemble finite residue
 let s:Finset (ℕ×ℕ):=((range (e+1)) ×ˢ range (e+3)).filter fun i=>Residual e n i.1 i.2
 have ht(i r)(hk:Residual e n i r):(i,r)∈s:=by unfold Residual Steam.taps at hk;simp only [s,mem_filter,mem_product,mem_range];constructor;exact ⟨by omega,by omega⟩;exact hk
 have hρ(i:↥s):=hc i.val.1 i.val.2 (Finset.mem_filter.mp i.property).2
 choose z hz H using hρ
 let a(i):=1+(c i+γ i+∑ j:↥s, z j i)
 have ha :D.Good a:=D.hear _ _ (D.steady _ zero_le_one) (D.hear _ _ (D.hear _ _ hB hγ) (crowd D univ z (fun j _=>hz j)))
 have hn0(i):0≤∑ j:↥s,z j i:=Finset.sum_nonneg fun j _=>D.safe _ (hz j) i
 have hh i:1≤a i ∧ c i ≤ a i ∧ γ i ≤ a i∧∀ j,z j i ≤ a i:=by
   have he0:=D.safe _ hB i;have he':=D.safe _ hγ i; unfold a
   refine ⟨by linarith [hn0 i],by linarith [hn0 i],by linarith [hn0 i],fun j=>?_⟩
   have hs:=single_le_sum (s:=univ) (f:=fun j:↥s=>z j i) (fun j _=>D.safe _ (hz j) i) (mem_univ j);linarith
 refine ⟨_,steadyPay D hb ha (fun i=>(hh i).1),fun i=>?_⟩
 let P:=a i
 have hm {V}{x x':ℝ}(hu:Wire (carpet (I i)) (w i) x V)(ht:x ≤ x'):Wire (carpet _) (w i) x' V:=by -- enlarge
    obtain ⟨hS,hQ,hU,hM⟩:=hu
    exact ⟨hS,hQ.trans ht,fun r=>(hU r).trans (by gcongr),fun r=>(hM r).trans (by gcongr)⟩
 have hS:WireCot (carpet (I i)) (w i) (d i) P (G i) (T i):=⟨hm (hT i).near (hh i).2.2.1,hm (hT i).far (hh i).2.2.1,hm (hT i).compare ((mul_le_mul_of_nonneg_right ((hh i).2.2.1) (hd i)))⟩
 have hx (V:Cables n (Market (I i)) (Market (J i))){p p':ℝ}(hh:Forms.street (lamp i (w i)) V (fun _=>p))(hp:p ≤ p'):Forms.street (lamp i (w i)) V (fun _=>p'):= by
    intro j;obtain ⟨hm,hV,hY⟩:=hh j;exact ⟨hm.trans hp,fun x=>(hV x).trans (by gcongr), fun x=>(hY x).trans (by gcongr)⟩
 obtain ⟨hk,hp,hq,hz,hA'⟩:=h i
 have hu: Alley (carpet _) (carpet _) (w i) (w i) (d i) P (lamp i (w i)) (repeatLine (p i) n) (repeatLine (q i) n):=⟨D.safe _ ha i,hx _ hp (hh i).2.1,hx _ hq (hh i).2.1,hx _ hz (mul_le_mul_of_nonneg_right ((hh i).2.1) (hd i)),hA'⟩
 exact (HP _ _ _ _ (d i) P (V i) _ _ _ _ _ _ (hV i) (hA i) hS hu (hd i) ((hh i).1) (fun k u ht' => let j:↥s:=⟨(k,u),ht k u ht'⟩; (H j i).mono le_rfl ((hh i).2.2.2 j) (hd i))).1
end YM.RG08.Ducat
