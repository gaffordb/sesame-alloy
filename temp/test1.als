sig Text {}

sig Cipher_Text extends Text{
    plain_text: one Plain_Text
}

sig Plain_Text extends Text{
    cipher_text: one Cipher_Text
}

pred invariant {
    all ct: Cipher_Text {
        all pt: Plain_Text {
            (ct.plain_text = pt) <=> (pt.cipher_text = ct)
        }
    }

}


run {
    invariant
    // #Cipher_Text > 5
} for 6